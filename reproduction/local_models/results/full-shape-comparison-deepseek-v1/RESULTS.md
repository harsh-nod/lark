# Independent full-size model comparison

**The original paper is not fully reproduced.** These are separate fixed-scaffold experiments.

Complete independent cohorts supplied: 1 of 6; this is not a paper-completion denominator.

| Model | Source | Level | Verified / tasks | Mean input M tokens, verified tasks | Mean output M tokens, verified tasks |
| --- | --- | --- | ---: | ---: | ---: |
| deepseek-ai/DeepSeek-V4.1-Flash-1017 | hip | level1 | 11 / 12 | 0.142809 | 0.021233 |
| deepseek-ai/DeepSeek-V4.1-Flash-1017 | hip | level2 | 5 / 5 | 0.296876 | 0.044669 |

Cohort totals below include every task, including budget exhaustions.

| Model | Source | Requests | All-task input M tokens | All-task output M tokens | First response / first actual Lean check verified |
| --- | --- | ---: | ---: | ---: | ---: |
| deepseek-ai/DeepSeek-V4.1-Flash-1017 | hip | 175 | 3.361778 | 0.482540 | 0 / 14 |

Mean input/output token costs include all responses, reads and failed proposals of each eventually verified task; budget-exhausted tasks are excluded from those means. All-task cohort totals retain failed-task costs. First response and first actual Lean check are separate metrics.

Independent fixed-scaffold tasks and existing generic proof libraries, three pinned open models and HIP/CUDA sources. Level2 includes dense SDPA, not the original FlashAttention algorithm. Packet hashes and recorded fresh-check bindings are checked here; no model/protocol/Lean/GPU experiment is rerun. This is not the original registry, PTX, closed-model histories, 144-cell result or NVIDIA measurement.
