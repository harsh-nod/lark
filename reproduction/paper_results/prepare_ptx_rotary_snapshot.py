"""Extend the frozen v26 auditor without changing its original-result assessments."""

import hashlib


BASELINE_AUDITOR_SHA256 = "7ecd1972d1046c730fda5b28f9eda8bf804122507042dfd2b7a0b7c9273b62cf"


def augment_auditor(source):
    if hashlib.sha256(source.encode()).hexdigest() != BASELINE_AUDITOR_SHA256:
        raise ValueError("Frozen v26 auditor integration point differs")
    additions = (
        ("    linear_checks = check_ptx_linear_evidence(config)\n",
         "    linear_checks = check_ptx_linear_evidence(config)\n"
         "    from ptx_rotary_release import check_ptx_rotary_evidence\n"
         "    rotary_checks = check_ptx_rotary_evidence(config)\n"),
        ('        "ptx_linear_evidence_checks": linear_checks,\n',
         '        "ptx_linear_evidence_checks": linear_checks,\n'
         '        "ptx_rotary_evidence_checks": rotary_checks,\n'),
        ('    linear = report["ptx_linear_evidence_checks"]\n',
         '    linear = report["ptx_linear_evidence_checks"]\n'
         '    rotary = report["ptx_rotary_evidence_checks"]\n'),
        ('        "ReLU, GEMV, GEMM, BMM and Linear are five independent full-size PTX development "\n',
         '        link("reproduction/ptx/results/full-size-rotary-proof-v1/RESULTS.md",\n'
         '             "Exact-source complete compiled FP16 interleaved RoPE proof")\n'
         '        + " adds one independent [256,128] development kernel with [256,64] sine/cosine "\n'
         '        + "inputs. All 51 instructions and 32768 lanes are covered, including initialized "\n'
         '        + "predicates, both branch paths, five actual memory accesses per lane and an "\n'
         '        + "independently defined reshape/select/stack/arithmetic/half tensor reference. Its "\n'
         '        + str(rotary["retained_positive_Main_checks"]) + " retained Main checks and "\n'
         '        + str(rotary["positive_rechecks"]) + " rechecks concern the same kernel. All "\n'
         '        + str(rotary["development_attempts"]) + " earlier development attempts, including "\n'
         '        + str(rotary["failed_development_checks"]) + " failures, remain separate. "\n'
         '        + rotary["scope"] + "\\n",\n'
         '        "ReLU, GEMV, GEMM, BMM, Linear and RoPE are six independent full-size PTX development "\n'),
    )
    for before, after in additions:
        if source.count(before) != 1:
            raise ValueError("Frozen v26 auditor integration point differs")
        source = source.replace(before, after)
    compile(source, "frozen-six-PTX-development-proof-auditor.py", "exec")
    return source
