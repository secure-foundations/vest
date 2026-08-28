PYTHON ?= python3
THREADS ?= 10

.PHONY: stats plots machine-info manifest verify-backend verify-cases runtime-smoke runtime cbor-runtime cbor-real-runtime asn1-runtime cms-runtime cms-real-runtime

stats:
	$(PYTHON) scripts/loc_stats.py
	$(PYTHON) scripts/summarize_verification.py
	$(PYTHON) scripts/summarize_backend_modules.py
	$(PYTHON) scripts/summarize_runtime.py
	$(PYTHON) scripts/summarize_scalability.py
	$(PYTHON) scripts/summarize_cbor_runtime.py
	$(PYTHON) scripts/summarize_asn1_runtime.py

plots: stats
	$(PYTHON) scripts/plot_runtime.py

machine-info:
	scripts/machine_info.sh

manifest:
	scripts/artifact_manifest.sh

verify-backend:
	scripts/verify_backend.sh $(THREADS)

verify-cases:
	scripts/verify_cases.sh $(THREADS)

runtime-smoke:
	cargo bench --manifest-path harnesses/vest-vps-runtime/Cargo.toml --bench vest_vps -- --test

runtime:
	scripts/run_vest_vps_runtime.sh

cbor-runtime:
	scripts/run_cbor_runtime.sh

cbor-real-runtime:
	scripts/run_cbor_real_runtime.sh

asn1-runtime:
	scripts/run_asn1_runtime.sh

cms-runtime:
	scripts/run_cms_runtime.sh

cms-real-runtime:
	scripts/run_cms_real_runtime.sh
