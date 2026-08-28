#!/usr/bin/env python3
import json
import os
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DERIVED_DIR = ROOT / "results" / "derived"
os.environ.setdefault("MPLCONFIGDIR", str(ROOT / "results/.matplotlib"))
os.environ.setdefault("XDG_CACHE_HOME", str(ROOT / "results/.cache"))
os.environ.setdefault("MPLBACKEND", "Agg")

import matplotlib.pyplot as plt
import numpy as np

with open(DERIVED_DIR / "asn1_cms_runtime.json", "r") as f:
    asn1_cms_data = json.load(f)

with open(DERIVED_DIR / "cbor_runtime.json", "r") as f:
    cbor_data = json.load(f)

with open(DERIVED_DIR / "cbor_real_runtime.json", "r") as f:
    cbor_real_data = json.load(f)

def get_entry(dataset, domain, operation, system):
    for entry in dataset:
        if domain is not None and entry.get("domain") != domain:
            continue
        if entry.get("operation") == operation and entry.get("system") == system:
            return entry
    raise ValueError(f"Entry not found: domain={domain}, op={operation}, system={system}")

def get_mibs_err(entry):
    mibs = entry["mib_per_second"]
    err = mibs * (entry["std_dev_nanoseconds"] / entry["nanoseconds"])
    return mibs, err

plt.rcParams.update({
    'font.family': 'sans-serif',
    'font.sans-serif': ['Helvetica', 'DejaVu Sans', 'Arial'],
    'font.size': 8,
    'axes.labelsize': 8.0,
    'axes.titlesize': 8.8,
    'xtick.labelsize': 7.2,
    'ytick.labelsize': 7.5,
    'legend.fontsize': 6.8,
    'figure.titlesize': 9.5,
    'pdf.fonttype': 42,
    'ps.fonttype': 42
})

c_vps = '#1b4965'      # Deep Midnight Slate (Ours)
c_base1 = '#62b6cb'    # Muted Teal (rasn / ciborium)
c_rc = '#84a98c'       # Soft Sage Green (RustCrypto / cbor4ii)
c_mini = '#e07a5f'     # Terracotta Coral (minicbor-serde)

err_style = dict(ecolor='#263238', elinewidth=0.9, capsize=2.5, capthick=0.9, alpha=0.9)

# Subplot width ratios
fig, axes = plt.subplots(
    1, 3,
    figsize=(7.0, 2.22),
    gridspec_kw={'width_ratios': [1.32, 0.90, 1.35]},
    constrained_layout=True
)

# -------------------------------------------------------------
# Panel 1: ASN.1 DER & BER
# -------------------------------------------------------------
ax1 = axes[0]
labels1 = ['DER\nParse', 'DER\nSer', 'BER Com.\nParse', 'BER Ext.\nParse']
x1 = np.array([0, 1, 2, 3])
w1 = 0.25
w1_ext = 0.32

vps_der_p, vps_der_p_err = get_mibs_err(get_entry(asn1_cms_data, "ASN.1 DER", "parse", "VPS"))
vps_der_s, vps_der_s_err = get_mibs_err(get_entry(asn1_cms_data, "ASN.1 DER", "serialize", "VPS"))
vps_ber_c, vps_ber_c_err = get_mibs_err(get_entry(asn1_cms_data, "ASN.1 BER common", "parse", "VPS"))
vps_ber_e, vps_ber_e_err = get_mibs_err(get_entry(asn1_cms_data, "ASN.1 BER comprehensive", "parse", "VPS"))

rasn_der_p, rasn_der_p_err = get_mibs_err(get_entry(asn1_cms_data, "ASN.1 DER", "parse", "rasn"))
rasn_der_s, rasn_der_s_err = get_mibs_err(get_entry(asn1_cms_data, "ASN.1 DER", "serialize", "rasn"))
rasn_ber_c, rasn_ber_c_err = get_mibs_err(get_entry(asn1_cms_data, "ASN.1 BER common", "parse", "rasn"))
rasn_ber_e, rasn_ber_e_err = get_mibs_err(get_entry(asn1_cms_data, "ASN.1 BER comprehensive", "parse", "rasn"))

rc_der_p, rc_der_p_err = get_mibs_err(get_entry(asn1_cms_data, "ASN.1 DER", "parse", "RustCrypto-der"))
rc_der_s, rc_der_s_err = get_mibs_err(get_entry(asn1_cms_data, "ASN.1 DER", "serialize", "RustCrypto-der"))
rc_ber_c, rc_ber_c_err = get_mibs_err(get_entry(asn1_cms_data, "ASN.1 BER common", "parse", "RustCrypto-ber"))

# Plot VPS
ax1.bar([0 - w1, 1 - w1, 2 - w1], [vps_der_p, vps_der_s, vps_ber_c], w1,
        yerr=[vps_der_p_err, vps_der_s_err, vps_ber_c_err], error_kw=err_style,
        label='VPS (Ours)', color=c_vps, edgecolor='#0f2838', linewidth=0.6)
ax1.bar([3 - 0.5*w1_ext], [vps_ber_e], w1_ext, yerr=[vps_ber_e_err], error_kw=err_style,
        color=c_vps, edgecolor='#0f2838', linewidth=0.6)

# Plot rasn
ax1.bar([0, 1, 2], [rasn_der_p, rasn_der_s, rasn_ber_c], w1,
        yerr=[rasn_der_p_err, rasn_der_s_err, rasn_ber_c_err], error_kw=err_style,
        label='rasn', color=c_base1, edgecolor='#3b707e', linewidth=0.6)
ax1.bar([3 + 0.5*w1_ext], [rasn_ber_e], w1_ext, yerr=[rasn_ber_e_err], error_kw=err_style,
        color=c_base1, edgecolor='#3b707e', linewidth=0.6)

# Plot RustCrypto
ax1.bar([0 + w1, 1 + w1, 2 + w1], [rc_der_p, rc_der_s, rc_ber_c], w1,
        yerr=[rc_der_p_err, rc_der_s_err, rc_ber_c_err], error_kw=err_style,
        label='RustCrypto', color=c_rc, edgecolor='#526b58', linewidth=0.6)

ax1.set_ylabel('Throughput (MiB/s)', fontweight='bold')
ax1.set_title('(a) ASN.1 DER & BER', fontweight='bold', pad=4)
ax1.set_xticks(x1)
ax1.set_xticklabels(labels1)
ax1.set_xlim(-0.6, 3.6)
ax1.set_ylim(0, 1720)
ax1.grid(axis='y', linestyle='--', alpha=0.35, color='gray')
ax1.set_axisbelow(True)
ax1.legend(frameon=True, loc='upper left', framealpha=0.95, facecolor='white', edgecolor='#cccccc',
           handlelength=1.0, handletextpad=0.25, borderpad=0.2, labelspacing=0.2)

# -------------------------------------------------------------
# Panel 2: CMS
# -------------------------------------------------------------
ax2 = axes[1]
labels2 = ['SignedData\nParse', 'SignedData\nSerialize']
x2 = np.arange(len(labels2))
w2 = 0.25

vps_cms_p, vps_cms_p_err = get_mibs_err(get_entry(asn1_cms_data, "CMS combined real corpus", "parse", "VPS"))
vps_cms_s, vps_cms_s_err = get_mibs_err(get_entry(asn1_cms_data, "CMS combined real corpus", "serialize", "VPS"))

rasn_cms_p, rasn_cms_p_err = get_mibs_err(get_entry(asn1_cms_data, "CMS combined real corpus", "parse", "rasn-cms"))
rasn_cms_s, rasn_cms_s_err = get_mibs_err(get_entry(asn1_cms_data, "CMS combined real corpus", "serialize", "rasn-cms"))

rc_cms_p, rc_cms_p_err = get_mibs_err(get_entry(asn1_cms_data, "CMS combined real corpus", "parse", "RustCrypto-cms"))
rc_cms_s, rc_cms_s_err = get_mibs_err(get_entry(asn1_cms_data, "CMS combined real corpus", "serialize", "RustCrypto-cms"))

ax2.bar(x2 - w2, [vps_cms_p, vps_cms_s], w2, yerr=[vps_cms_p_err, vps_cms_s_err], error_kw=err_style,
        label='VPS (Ours)', color=c_vps, edgecolor='#0f2838', linewidth=0.6)
ax2.bar(x2, [rasn_cms_p, rasn_cms_s], w2, yerr=[rasn_cms_p_err, rasn_cms_s_err], error_kw=err_style,
        label='rasn-cms', color=c_base1, edgecolor='#3b707e', linewidth=0.6)
ax2.bar(x2 + w2, [rc_cms_p, rc_cms_s], w2, yerr=[rc_cms_p_err, rc_cms_s_err], error_kw=err_style,
        label='RustCrypto-cms', color=c_rc, edgecolor='#526b58', linewidth=0.6)

ax2.set_ylabel('Throughput (MiB/s)', fontweight='bold')
ax2.set_title('(b) CMS', fontweight='bold', pad=4)
ax2.set_xticks(x2)
ax2.set_xticklabels(labels2)
ax2.set_xlim(-0.55, 1.55)
ax2.set_ylim(0, 8000)
ax2.grid(axis='y', linestyle='--', alpha=0.35, color='gray')
ax2.set_axisbelow(True)
ax2.legend(frameon=True, loc='upper left', framealpha=0.95, facecolor='white', edgecolor='#cccccc',
           handlelength=1.0, handletextpad=0.25, borderpad=0.2, labelspacing=0.2)

# -------------------------------------------------------------
# Panel 3: CBOR & COSE
# -------------------------------------------------------------
ax3 = axes[2]
labels3 = ['CBOR\nParse', 'CBOR\nSer', 'COSE\nParse', 'COSE\nSer']
x3 = np.array([0, 1, 2, 3])

w_cbor = 0.21
w_cose = 0.30

# Load Generic CBOR
vps_cbor_p, vps_cbor_p_err = get_mibs_err(get_entry(cbor_data, None, "parse", "VPS"))
vps_cbor_s, vps_cbor_s_err = get_mibs_err(get_entry(cbor_data, None, "serialize", "VPS"))

cib_cbor_p, cib_cbor_p_err = get_mibs_err(get_entry(cbor_data, None, "parse", "ciborium"))
cib_cbor_s, cib_cbor_s_err = get_mibs_err(get_entry(cbor_data, None, "serialize", "ciborium"))

cbor4ii_p, cbor4ii_p_err = get_mibs_err(get_entry(cbor_data, None, "parse", "cbor4ii"))
cbor4ii_s, cbor4ii_s_err = get_mibs_err(get_entry(cbor_data, None, "serialize", "cbor4ii"))

mini_cbor_p, mini_cbor_p_err = get_mibs_err(get_entry(cbor_data, None, "parse", "minicbor-serde"))
mini_cbor_s, mini_cbor_s_err = get_mibs_err(get_entry(cbor_data, None, "serialize", "minicbor-serde"))

# Load COSE
vps_cose_p, vps_cose_p_err = get_mibs_err(get_entry(cbor_real_data, None, "parse", "VPS"))
vps_cose_s, vps_cose_s_err = get_mibs_err(get_entry(cbor_real_data, None, "serialize", "VPS"))

cib_cose_p, cib_cose_p_err = get_mibs_err(get_entry(cbor_real_data, None, "parse", "ciborium"))
cib_cose_s, cib_cose_s_err = get_mibs_err(get_entry(cbor_real_data, None, "serialize", "ciborium"))

# Plot VPS
ax3.bar([0 - 1.5*w_cbor, 1 - 1.5*w_cbor], [vps_cbor_p, vps_cbor_s], w_cbor,
        yerr=[vps_cbor_p_err, vps_cbor_s_err], error_kw=err_style,
        label='VPS (Ours)', color=c_vps, edgecolor='#0f2838', linewidth=0.6)
ax3.bar([2 - 0.5*w_cose, 3 - 0.5*w_cose], [vps_cose_p, vps_cose_s], w_cose,
        yerr=[vps_cose_p_err, vps_cose_s_err], error_kw=err_style,
        color=c_vps, edgecolor='#0f2838', linewidth=0.6)

# Plot ciborium
ax3.bar([0 - 0.5*w_cbor, 1 - 0.5*w_cbor], [cib_cbor_p, cib_cbor_s], w_cbor,
        yerr=[cib_cbor_p_err, cib_cbor_s_err], error_kw=err_style,
        label='ciborium', color=c_base1, edgecolor='#3b707e', linewidth=0.6)
ax3.bar([2 + 0.5*w_cose, 3 + 0.5*w_cose], [cib_cose_p, cib_cose_s], w_cose,
        yerr=[cib_cose_p_err, cib_cose_s_err], error_kw=err_style,
        color=c_base1, edgecolor='#3b707e', linewidth=0.6)

# Plot cbor4ii
ax3.bar([0 + 0.5*w_cbor, 1 + 0.5*w_cbor], [cbor4ii_p, cbor4ii_s], w_cbor,
        yerr=[cbor4ii_p_err, cbor4ii_s_err], error_kw=err_style,
        label='cbor4ii', color=c_rc, edgecolor='#526b58', linewidth=0.6)

# Plot minicbor-serde
ax3.bar([0 + 1.5*w_cbor, 1 + 1.5*w_cbor], [mini_cbor_p, mini_cbor_s], w_cbor,
        yerr=[mini_cbor_p_err, mini_cbor_s_err], error_kw=err_style,
        label='minicbor', color=c_mini, edgecolor='#9e533e', linewidth=0.6)

ax3.set_ylabel('Throughput (MiB/s)', fontweight='bold')
ax3.set_title('(c) CBOR & COSE', fontweight='bold', pad=4)
ax3.set_xticks(x3)
ax3.set_xticklabels(labels3)
ax3.set_xlim(-0.6, 3.6)
ax3.set_ylim(0, 1500)
ax3.grid(axis='y', linestyle='--', alpha=0.35, color='gray')
ax3.set_axisbelow(True)

ax3.legend(frameon=True, loc='upper left', ncol=2, columnspacing=0.7, framealpha=0.95, facecolor='white',
           edgecolor='#cccccc', handlelength=0.9, handletextpad=0.2, borderpad=0.25, labelspacing=0.2)

output = ROOT / "results" / "figures" / "eval_runtime.pdf"
output.parent.mkdir(parents=True, exist_ok=True)
plt.savefig(output)
plt.close()
print(f"Regenerated {output}")
