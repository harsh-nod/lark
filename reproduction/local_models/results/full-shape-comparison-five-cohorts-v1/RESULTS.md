# Independent full-size model comparison

**The original paper is not fully reproduced.** These are separate fixed-scaffold experiments.

Complete independent cohorts supplied: 5 of 6; this is not a paper-completion denominator.

| Model | Source | Level | Verified / tasks | Mean input M tokens, verified tasks | Mean output M tokens, verified tasks |
| --- | --- | --- | ---: | ---: | ---: |
| deepseek-ai/DeepSeek-V4.1-Flash-1017 | hip | level1 | 11 / 12 | 0.142809 | 0.021233 |
| deepseek-ai/DeepSeek-V4.1-Flash-1017 | hip | level2 | 5 / 5 | 0.296876 | 0.044669 |
| zai-org/GLM-5.3-Flash | hip | level1 | 9 / 12 | 0.081640 | 0.005264 |
| zai-org/GLM-5.3-Flash | hip | level2 | 3 / 5 | 0.120210 | 0.005286 |
| zai-org/GLM-5.3-Flash | cuda | level1 | 5 / 12 | 0.072328 | 0.006827 |
| zai-org/GLM-5.3-Flash | cuda | level2 | 4 / 5 | 0.106352 | 0.005578 |
| zai-org/GLM-5.3 | hip | level1 | 10 / 12 | 0.108794 | 0.018695 |
| zai-org/GLM-5.3 | hip | level2 | 5 / 5 | 0.137481 | 0.009095 |
| deepseek-ai/DeepSeek-V4.1-Flash-1017 | cuda | level1 | 12 / 12 | 0.157094 | 0.027157 |
| deepseek-ai/DeepSeek-V4.1-Flash-1017 | cuda | level2 | 5 / 5 | 0.207996 | 0.026377 |

Cohort totals below include every task, including budget exhaustions.

| Model | Source | Requests | All-task input M tokens | All-task output M tokens | First response / first actual Lean check verified |
| --- | --- | ---: | ---: | ---: | ---: |
| deepseek-ai/DeepSeek-V4.1-Flash-1017 | hip | 175 | 3.361778 | 0.482540 | 0 / 14 |
| zai-org/GLM-5.3-Flash | hip | 93 | 1.563506 | 0.115224 | 0 / 5 |
| zai-org/GLM-5.3-Flash | cuda | 108 | 1.841471 | 0.164371 | 0 / 3 |
| zai-org/GLM-5.3 | hip | 123 | 2.090532 | 0.245080 | 0 / 12 |
| deepseek-ai/DeepSeek-V4.1-Flash-1017 | cuda | 160 | 2.925108 | 0.457767 | 0 / 12 |

Mean input/output token costs include all responses, reads and failed proposals of each eventually verified task; budget-exhausted tasks are excluded from those means. All-task cohort totals retain failed-task costs. First response and first actual Lean check are separate metrics.

Independent fixed-scaffold tasks and existing generic proof libraries, three pinned open models and HIP/CUDA sources. Level2 includes dense SDPA, not the original FlashAttention algorithm. Packet hashes and recorded fresh-check bindings are checked here; no model/protocol/Lean/GPU experiment is rerun. This is not the original registry, PTX, closed-model histories, 144-cell result or NVIDIA measurement.
