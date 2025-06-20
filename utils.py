import re
from typing import List, Optional
import json
import pickle
import os

class LeanTheoremGenerator:
    """
    A class to generate Lean theorem statements about implications between algebraic equations.

    This class stores a list of equations and a matrix of their implication relationships.
    It can then generate Lean code to prove or disprove that one equation implies another.

    Attributes:
        implications (List[List[str]]): A matrix indicating the implication status
            between equations (e.g., "explicit_proof_true").
        equations (List[str]): A list of string representations of the equations.
    """
    _TEMPLATE = """
import Mathlib.Tactic

class Magma (α : Type _) where
  op : α → α → α

infix:65 " ◇ " => Magma.op

abbrev EquationEQ1 (G: Type _) [Magma G] := ∀ CODE1

abbrev EquationEQ2 (G: Type _) [Magma G] := ∀ CODE2
"""

    _TEMPLATE_YES = """
theorem EquationEQ1_implies_EquationEQ2 (G: Type _) [Magma G] (h: EquationEQ1 G) : EquationEQ2 G := by
  sorry
"""

    _TEMPLATE_NO = """
theorem EquationEQ1_not_implies_EquationEQ2 : ∃ (G: Type) (_: Magma G), EquationEQ1 G ∧ ¬ EquationEQ2 G := by
  sorry
"""

    def __init__(self, implications: List[List[str]], equations: List[str]):
        """
        Initializes the LeanTheoremGenerator with equations and their implication matrix.
        Args:
            implications: A list of lists representing the implication matrix.
            equations: A list of equations as strings.
        """
        self.implications = implications
        self.equations = equations

    def _convert_equation(self, equation_str: str):
        """
        Extracts and formats an equation from a string for the Lean template.
        Args:
            equation_str: The string containing the equation (e.g., "a*b = b*a").
        Returns:
            A formatted string for the Lean template (e.g., "a b : G, a * b = b * a").
        """
        # equation_match = re.search(r'\[(.*?)\]', equation_str)
        # if not equation_match:
        #     raise ValueError("Invalid equation format. Expected format: '[left=right]'")

        # equation = equation_match.group(1)
        left, right = [s.strip() for s in equation_str.split('=')]
        variables = sorted(list(set(re.findall(r'[a-z]', equation_str))))

        return f"{' '.join(variables)} : G, {left} = {right}"

    def prepare_statement(self, source_idx: int, target_idx: int):
        """
        Generates a Lean problem statement for a specific implication.
        Args:
            source_idx: The index of the source equation in the `equations` list.
            target_idx: The index of the target equation in the `equations` list.
        Returns:
            A string containing the complete Lean problem statement.
        """
        implication_status = self.implications[source_idx][target_idx]
        
        direction: Optional[bool] = None
        if "true" in implication_status:
            direction = True
        elif "false" in implication_status:
            direction = False

        if direction is True:
            template = self._TEMPLATE + self._TEMPLATE_YES
        elif direction is False:
            template = self._TEMPLATE + self._TEMPLATE_NO
        else:
            raise ValueError("Invalid implication status. Expected 'true' or 'false'.")

        string = template.replace('EQ1', str(source_idx + 1)).replace('EQ2', str(target_idx + 1))
        string = string.replace("CODE1", self._convert_equation(self.equations[source_idx]))
        string = string.replace("CODE2", self._convert_equation(self.equations[target_idx]))
        return string


def get_theorem_generator(implications_file="/data2/haikang/projects/cloned/equational_theories/data/outcomes.json",
                          equations_file="/data2/haikang/projects/cloned/equational_theories/data/equations.txt",
                          cached_generator_file="theorem_generator.pkl"):
    if not os.path.exists(cached_generator_file):
        with open(implications_file, 'r') as f:
            implications = json.load(f)["outcomes"]

        with open(equations_file, 'r') as f:
            equations = [line.strip() for line in f.readlines()]

        generator = LeanTheoremGenerator(implications, equations)

        with open(cached_generator_file, 'wb') as f:
            pickle.dump(generator, f)
    else:
        with open(cached_generator_file, 'rb') as f:
            generator = pickle.load(f)
    return generator


def format_prompt(statement: str, cot: bool):
    if cot:
        prompt = """
Complete the following Lean 4 code:

```lean4
{}
```

Before producing the Lean 4 code to formally prove the given theorem, provide a detailed proof plan outlining the main proof steps and strategies.
The plan should highlight key ideas, intermediate lemmas, and proof structures that will guide the construction of the final formal proof.
""".strip()
    else:
        prompt = """
Complete the following Lean 4 code:

```lean4
{}
```
""".strip()

    return prompt.format(statement)
