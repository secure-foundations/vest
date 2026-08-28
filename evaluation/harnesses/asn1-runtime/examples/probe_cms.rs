use der::Decode;
use std::{
    collections::BTreeMap,
    fs,
    path::{Path, PathBuf},
};
use vps_lib::asn1::tag::tag_num_from_uint;
use vps_lib::asn1::{Class, Retaggable, Tag};
use vps_lib::core::exec::Parser;
use vps_asn1_runtime_eval::{generated_cms_ber, generated_cms_der};

fn files(root: &Path, result: &mut Vec<PathBuf>) {
    for entry in fs::read_dir(root).unwrap() {
        let path = entry.unwrap().path();
        if path.is_dir() {
            files(&path, result);
        } else if matches!(
            path.extension()
                .and_then(|x| x.to_str())
                .map(str::to_ascii_lowercase)
                .as_deref(),
            Some("p7m" | "p7s" | "cms" | "pkcs7" | "bin")
        ) {
            result.push(path);
        }
    }
}

fn header(input: &[u8], offset: usize) -> Option<(usize, Option<usize>)> {
    let mut pos = offset + 1;
    if input.get(offset)? & 31 == 31 {
        while input.get(pos)? & 0x80 != 0 {
            pos += 1;
        }
        pos += 1;
    }
    let first = *input.get(pos)?;
    pos += 1;
    if first == 0x80 {
        return Some((pos, None));
    }
    if first & 0x80 == 0 {
        return Some((pos, Some(first as usize)));
    }
    let count = (first & 0x7f) as usize;
    let mut len = 0usize;
    for byte in input.get(pos..pos + count)? {
        len = (len << 8) | *byte as usize;
    }
    Some((pos + count, Some(len)))
}

fn end(input: &[u8], offset: usize) -> Option<usize> {
    let (start, len) = header(input, offset)?;
    if let Some(len) = len {
        return start.checked_add(len).filter(|end| *end <= input.len());
    }
    let mut pos = start;
    loop {
        if input.get(pos..pos + 2)? == [0, 0] {
            return Some(pos + 2);
        }
        pos = end(input, pos)?;
    }
}

fn signed_data(input: &[u8]) -> Option<&[u8]> {
    if input.first() != Some(&0x30) {
        return None;
    }
    let (outer, _) = header(input, 0)?;
    if input.get(outer)? != &0x06 {
        return None;
    }
    let explicit = end(input, outer)?;
    if input.get(explicit)? != &0xa0 {
        return None;
    }
    let (inner, _) = header(input, explicit)?;
    let inner_end = end(input, inner)?;
    Some(&input[inner..inner_end])
}

fn certificate_tlvs(signed: &[u8]) -> Vec<&[u8]> {
    let Some((mut pos, len)) = header(signed, 0) else {
        return Vec::new();
    };
    let limit = len.map_or(signed.len(), |len| pos + len);
    for _ in 0..3 {
        let Some(next) = end(signed, pos) else {
            return Vec::new();
        };
        pos = next;
    }
    if pos >= limit || signed[pos] != 0xa0 {
        return Vec::new();
    }
    let Some((mut child, child_len)) = header(signed, pos) else {
        return Vec::new();
    };
    let child_limit =
        child_len.map_or_else(|| end(signed, pos).unwrap_or(child), |len| child + len);
    let mut result = Vec::new();
    while child < child_limit {
        let Some(next) = end(signed, child) else {
            break;
        };
        result.push(&signed[child..next]);
        child = next;
    }
    result
}

fn sequence_children(input: &[u8]) -> Vec<&[u8]> {
    let Some((mut pos, len)) = header(input, 0) else {
        return Vec::new();
    };
    let limit = len.map_or(input.len(), |len| pos + len);
    let mut result = Vec::new();
    while pos < limit {
        let Some(next) = end(input, pos) else { break };
        result.push(&input[pos..next]);
        pos = next;
    }
    result
}

fn main() {
    for root in std::env::args().skip(1) {
        let mut paths = Vec::new();
        files(Path::new(&root), &mut paths);
        paths.sort();
        let mut counts = [0usize; 6];
        let mut bytes = [0usize; 6];
        let mut der_common = Vec::new();
        let mut ber_common = Vec::new();
        let mut ber_vps_rasn = Vec::new();
        let mut vps_der_errors = BTreeMap::new();
        let mut vps_ber_errors = BTreeMap::new();
        let mut vps_rejected = Vec::new();
        let mut rejected_certificate_counts = BTreeMap::new();
        let mut rejected_component_counts = BTreeMap::new();
        for path in &paths {
            let input = fs::read(path).unwrap();
            let Some(signed) = signed_data(&input) else {
                continue;
            };
            let vps_der = generated_cms_der::SIGNED_DATA::Fmt.parse(&&signed[..]);
            let vps_ber = generated_cms_ber::SIGNED_DATA::Fmt.parse(&&signed[..]);
            if let Err(error) = &vps_der {
                *vps_der_errors
                    .entry(format!("{:?}: {:?}", error.kind, error.failed_format))
                    .or_insert(0usize) += 1;
                vps_rejected.push(path.clone());
                for certificate in certificate_tlvs(signed) {
                    let accepted = generated_cms_der::CERTIFICATE::Fmt
                        .parse(&certificate)
                        .is_ok();
                    *rejected_certificate_counts
                        .entry(accepted)
                        .or_insert(0usize) += 1;
                }
                let children = sequence_children(signed);
                if children.len() >= 4 {
                    let checks = [
                        (
                            "version",
                            generated_cms_der::CMS_VERSION::Fmt
                                .parse(&children[0])
                                .is_ok(),
                        ),
                        (
                            "digests",
                            generated_cms_der::DIGEST_ALGORITHM_IDENTIFIERS::Fmt
                                .parse(&children[1])
                                .is_ok(),
                        ),
                        (
                            "encap",
                            generated_cms_der::ENCAPSULATED_CONTENT_INFO::Fmt
                                .parse(&children[2])
                                .is_ok(),
                        ),
                        (
                            "signers",
                            generated_cms_der::SIGNER_INFOS::Fmt
                                .parse(children.last().unwrap())
                                .is_ok(),
                        ),
                    ];
                    for (name, accepted) in checks {
                        *rejected_component_counts
                            .entry((name, accepted))
                            .or_insert(0usize) += 1;
                    }
                    if let Some(certificates) =
                        children.iter().find(|child| child.first() == Some(&0xa0))
                    {
                        let fmt = generated_cms_der::CERTIFICATE_SET::Fmt.retagged(Tag {
                            class: Class::ContextSpecific,
                            constructed: true,
                            number: tag_num_from_uint(0),
                        });
                        let result = fmt.parse(certificates);
                        *rejected_component_counts
                            .entry(("certificate-set", result.is_ok()))
                            .or_insert(0usize) += 1;
                        if let Err(error) = result {
                            *vps_der_errors
                                .entry(format!("certificate-set: {:?}", error.kind))
                                .or_insert(0usize) += 1;
                        }
                    }
                }
            }
            if let Err(error) = &vps_ber {
                *vps_ber_errors
                    .entry(format!("{:?}: {:?}", error.kind, error.failed_format))
                    .or_insert(0usize) += 1;
            }
            let checks = [
                vps_der.is_ok(),
                vps_ber.is_ok(),
                rasn::der::decode::<rasn_cms::SignedData>(signed).is_ok(),
                rasn::ber::decode::<rasn_cms::SignedData>(signed).is_ok(),
                rustcrypto_cms::signed_data::SignedData::from_der(signed).is_ok(),
                rustcrypto_cms::signed_data::SignedData::from_ber(signed).is_ok(),
            ];
            for (i, accepted) in checks.iter().copied().enumerate() {
                if accepted {
                    counts[i] += 1;
                    bytes[i] += signed.len();
                }
            }
            if checks[0] && checks[2] && checks[4] {
                der_common.push((path, signed.len()));
            }
            if checks[1] && checks[3] && checks[5] {
                ber_common.push((path, signed.len()));
            }
            if checks[1] && checks[3] {
                ber_vps_rasn.push((path, signed.len()));
            }
        }
        println!(
            "{root}: files={} signed={} counts={counts:?} bytes={bytes:?}",
            paths.len(),
            paths
                .iter()
                .filter(|p| signed_data(&fs::read(p).unwrap()).is_some())
                .count()
        );
        println!("  VPS DER rejection paths: {vps_der_errors:?}");
        println!("  VPS BER rejection paths: {vps_ber_errors:?}");
        println!("  Certificates inside VPS-rejected messages (accepted => count): {rejected_certificate_counts:?}");
        println!("  Components inside VPS-rejected messages ((component, accepted) => count): {rejected_component_counts:?}");
        for path in vps_rejected.iter().take(10) {
            println!("  VPS rejected: {}", path.display());
        }
        for (name, selected) in [
            ("der-common", &der_common),
            ("ber-common", &ber_common),
            ("ber-vps-rasn", &ber_vps_rasn),
        ] {
            println!(
                "  {name}: files={} bytes={}",
                selected.len(),
                selected.iter().map(|x| x.1).sum::<usize>()
            );
            for (path, _) in selected {
                println!("    {}", path.display());
            }
        }
    }
}
