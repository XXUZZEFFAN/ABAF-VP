# ABAF-VP Supplementary Experimental Materials

This repository contains the recorded experimental data, result tables, selected rule implementations, and portable analysis scripts accompanying the ABAF-VP study. It supports independent recomputation of the reported statistics from the supplied experimental outputs.

The materials correspond to the final experimental versions `exp1_recommendation_v2`, `exp2_ablation_v1`, `exp3_rule_alignment_v5`, `exp4_execution_cost_v1`, and `exp4_execution_cost_v2`.

## Repository contents

| Directory | Contents |
| --- | --- |
| `recommendation/` | 100 tasks, 176 candidate plans, reference labels, full ranked plan IDs, and results for B0–B4 (500 method–task records). |
| `ablation/` | FULL and three ablations on the same 100 tasks (400 records, including the FULL reference). A1 removes mechanism matching, A2 removes oracle adaptation, and A3 removes prior evidence. |
| `paired/` | Final outcomes for 60 bug/fix pairs and 120 sides, original B4 outcomes, case/version identifiers, target contracts, 43 alignment bindings, the rule registry, and rule implementation source. |
| `timing/` | Five-method and aligned-system timing summaries, task and physical-run receipts, input-preparation timings, timing coverage, and the deduplicated operation ledger. |
| `scripts/` | Portable metric and statistical calculations using only the Python standard library. |

CSV files contain tabular data. JSONL files contain one JSON object per line.

## Requirements

- Python 3.9 or later
- No third-party Python packages

## Recompute the reported statistics

From the repository root, run:

```sh
python3 scripts/recompute.py
```

The script writes recomputed CSV tables and `summary.json` to `recomputed/`. To choose another output directory:

```sh
python3 scripts/recompute.py --output /path/to/results
```

The script:

- calculates recommendation metrics from ranked plan IDs and reference labels;
- reproduces cluster bootstrap intervals and paired permutation tests with Holm correction;
- summarizes final pair classifications and execution outcomes;
- recalculates known machine time from the recorded receipts; and
- checks recomputed values against the supplied result tables using assertions.

A successful run prints a JSON summary and the output directory. The bootstrap and permutation calculations use recorded random seeds.

## Reading the results

### Recommendation and ablation

B0 is category mapping, B1 is BM25, B2 is embedding similarity, B3 is capability matching, and B4 is the complete planner. Recommendation P@1, Success@3, and MRR use the 13 jointly solvable tasks. A reference is accepted if it is `VALID`, or `CONDITIONAL` with an explicitly satisfied condition. The retained `DEV` value is the original stored split label for the 100-task evaluation.

### Paired verification

Pair success uses the final `MATCHED` classification. Original B4 verifies 5/60 pairs; B4+ALIGN verifies 47/60, including 26/36 real-world and 21/24 benchmark pairs. The other final classes are `PROPERTY_SUPPORT` (1), `NOT_APPLICABLE` (10), and `UNRESOLVED` (2).

Rule selection and target binding were manually configured. FP-32 retains its final adjudicated classification; contract details are supplied in `paired/target_contracts.jsonl`.

### Timing

Timing is measured in seconds. Shared physical runs and input identities are counted once per method. For the aligned total, the rounded tool and preparation totals are combined with checker and AST time, as in the recorded analysis. The alignment increment is 30.273963 s and total known machine time is 582.609963 s. Missing timing values remain null, including manual configuration time.

## Scope and limitations

- The reproduction command recalculates statistics from recorded experimental outputs; it does not rerun the complete planner, Android detectors, or original bug/fix experiments.
- Original Android source snapshots and detector installations are not included and are not required for the statistical recomputation.
- Local absolute paths in provenance fields have been replaced by relative `original_workspace/` or `original_tmp/` paths for privacy. They are historical identifiers, not directories required by the reproduction command. Paths inside third-party containers are retained as published by those tools.
- The supplied rule implementations and analysis scripts should not be interpreted as a complete release of the ABAF-VP system.

## License

Analysis code is provided under the MIT License. Experimental data and documentation are provided under CC BY 4.0, except where third-party terms apply. See `LICENSE` for details.
