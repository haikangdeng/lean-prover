## Notes

Clone Terry's [ETP repository](https://github.com/teorth/equational_theories), navigate to `data/`, unzip the latest (2024-11-10) `edge-list.csv.zip` and `outcomes.json.zip`, come back to this repo and replace the file directories for the `get_theorem_generator()` function in `utils.py` with the inflated files.

`100_samples.json` contains 100 edges sampled from Terry's ETP graph, where index N maps to Equation(N+1). No need to worry about the offset as the LeanTheoremGenerator is also 0-indexed.
