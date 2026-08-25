# ASN.1 and CMS runtime

ASN.1 uses 1,024 typed records. The common BER corpus is accepted by all three parsers; the comprehensive corpus additionally exercises legal forms that RustCrypto's deliberately restricted BER decoder rejects. BER serialization reports normalized definite output. Synthetic CMS uses 1,024 `id-data` ContentInfo values. The real CMS rows use three independently attributed SignedData corpora: official NIST PKITS S/MIME cases, European Commission DSS CAdES fixtures, and RFC 4134 examples. Each row uses the exact common input intersection accepted by all three implementations. The combined rows are directly sampled over the concatenation of all three strata.

| Domain | Operation | Implementation | Time | MiB/s | Throughput relative to VPS |
|---|---|---|---:|---:|---:|
| ASN.1 DER | parse | VPS | 211.66 ± 4.86 µs | 828.0 | 1.00× |
| ASN.1 DER | parse | rasn | 238.27 ± 4.88 µs | 735.5 | 0.89× |
| ASN.1 DER | parse | RustCrypto-der | 312.80 ± 6.83 µs | 560.3 | 0.68× |
| ASN.1 DER | serialize | VPS | 139.47 ± 1.95 µs | 1256.6 | 1.00× |
| ASN.1 DER | serialize | rasn | 427.60 ± 41.76 µs | 409.9 | 0.33× |
| ASN.1 DER | serialize | RustCrypto-der | 215.49 ± 3.37 µs | 813.3 | 0.65× |
| ASN.1 BER common | parse | VPS | 285.35 ± 2.98 µs | 622.7 | 1.00× |
| ASN.1 BER common | parse | rasn | 265.80 ± 5.00 µs | 668.5 | 1.07× |
| ASN.1 BER common | parse | RustCrypto-ber | 461.18 ± 8.12 µs | 385.3 | 0.62× |
| ASN.1 BER comprehensive | parse | VPS | 308.83 ± 5.38 µs | 578.3 | 1.00× |
| ASN.1 BER comprehensive | parse | rasn | 282.14 ± 3.40 µs | 633.0 | 1.09× |
| ASN.1 BER normalized output | serialize | VPS | 132.76 ± 1.83 µs | 1320.2 | 1.00× |
| ASN.1 BER normalized output | serialize | rasn | 418.92 ± 5.71 µs | 418.4 | 0.32× |
| CMS ContentInfo DER | parse | VPS | 90.89 ± 1.18 µs | 2969.1 | 1.00× |
| CMS ContentInfo DER | parse | rasn-cms | 104.10 ± 1.48 µs | 2592.3 | 0.87× |
| CMS ContentInfo DER | parse | RustCrypto-cms | 91.05 ± 1.06 µs | 2963.8 | 1.00× |
| CMS ContentInfo DER | parse | cryptographic-message-syntax | 87.66 ± 1.44 µs | 3078.3 | 1.04× |
| CMS ContentInfo DER | serialize | VPS | 40.86 ± 1.68 µs | 6604.3 | 1.00× |
| CMS ContentInfo DER | serialize | rasn-cms | 216.06 ± 97.62 µs | 1248.9 | 0.19× |
| CMS ContentInfo DER | serialize | RustCrypto-cms | 40.26 ± 0.86 µs | 6703.1 | 1.01× |
| CMS ContentInfo DER | serialize | cryptographic-message-syntax | 12.32 ± 0.37 µs | 21894.2 | 3.32× |
| CMS NIST PKITS | parse | VPS | 1575.57 ± 44.85 µs | 577.8 | 1.00× |
| CMS NIST PKITS | parse | rasn-cms | 2162.05 ± 563.11 µs | 421.0 | 0.73× |
| CMS NIST PKITS | parse | RustCrypto-cms | 2038.02 ± 29.65 µs | 446.7 | 0.77× |
| CMS EC DSS CAdES | parse | VPS | 1036.78 ± 14.91 µs | 10486.6 | 1.00× |
| CMS EC DSS CAdES | parse | rasn-cms | 2159.17 ± 34.64 µs | 5035.4 | 0.48× |
| CMS EC DSS CAdES | parse | RustCrypto-cms | 2141.20 ± 38.64 µs | 5077.7 | 0.48× |
| CMS RFC 4134 | parse | VPS | 15.42 ± 0.72 µs | 515.3 | 1.00× |
| CMS RFC 4134 | parse | rasn-cms | 19.43 ± 0.62 µs | 409.0 | 0.79× |
| CMS RFC 4134 | parse | RustCrypto-cms | 19.82 ± 0.19 µs | 400.8 | 0.78× |
| CMS combined real corpus | parse | VPS | 2643.07 ± 31.30 µs | 4460.9 | 1.00× |
| CMS combined real corpus | parse | rasn-cms | 4337.50 ± 52.07 µs | 2718.3 | 0.61× |
| CMS combined real corpus | parse | RustCrypto-cms | 4204.41 ± 68.49 µs | 2804.3 | 0.63× |
| CMS NIST PKITS | serialize | VPS | 992.20 ± 16.60 µs | 917.5 | 1.00× |
| CMS NIST PKITS | serialize | rasn-cms | 4534.33 ± 117.78 µs | 200.8 | 0.22× |
| CMS NIST PKITS | serialize | RustCrypto-cms | 964.15 ± 21.21 µs | 944.1 | 1.03× |
| CMS EC DSS CAdES | serialize | VPS | 979.87 ± 16.80 µs | 11094.9 | 1.00× |
| CMS EC DSS CAdES | serialize | rasn-cms | 4771.85 ± 111.81 µs | 2278.3 | 0.21× |
| CMS EC DSS CAdES | serialize | RustCrypto-cms | 1044.08 ± 32.06 µs | 10412.6 | 0.94× |
| CMS RFC 4134 | serialize | VPS | 9.23 ± 0.12 µs | 859.6 | 1.00× |
| CMS RFC 4134 | serialize | rasn-cms | 38.70 ± 0.56 µs | 205.1 | 0.24× |
| CMS RFC 4134 | serialize | RustCrypto-cms | 8.28 ± 0.70 µs | 958.7 | 1.12× |
| CMS combined real corpus | serialize | VPS | 1977.92 ± 44.53 µs | 5960.7 | 1.00× |
| CMS combined real corpus | serialize | rasn-cms | 8971.97 ± 211.96 µs | 1314.1 | 0.22× |
| CMS combined real corpus | serialize | RustCrypto-cms | 1975.06 ± 64.09 µs | 5969.4 | 1.00× |
