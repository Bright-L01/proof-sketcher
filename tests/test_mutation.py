"""Mutation testing for test quality verification.

This module implements mutation testing to ensure our tests can actually
catch bugs by introducing small changes (mutations) to the code and
verifying that tests fail.
"""

import ast
import copy
import subprocess
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Optional, Set, Tuple

import pytest


@dataclass
class Mutation:
    """Represents a single mutation."""

    file_path: Path
    line_number: int
    original_code: str
    mutated_code: str
    mutation_type: str
    description: str

    @property
    def id(self) -> str:
        """Generate unique ID for mutation."""
        return f"{self.file_path.stem}:{self.line_number}:{self.mutation_type}"


@dataclass
class MutationResult:
    """Result of testing a mutation."""

    mutation: Mutation
    killed: bool  # True if tests caught the mutation
    test_output: str
    execution_time: float
    failing_tests: List[str] = None

    @property
    def survived(self) -> bool:
        """True if mutation survived (tests didn't catch it)."""
        return not self.killed


class MutationOperator:
    """Base class for mutation operators."""

    def mutate(self, node: ast.AST) -> Optional[ast.AST]:
        """Apply mutation to an AST node.

        Args:
            node: AST node to mutate

        Returns:
            Mutated node or None if mutation not applicable
        """
        raise NotImplementedError


class ArithmeticOperatorMutation(MutationOperator):
    """Mutate arithmetic operators."""

    MUTATIONS = {
        ast.Add: [ast.Sub, ast.Mult],
        ast.Sub: [ast.Add, ast.Mult],
        ast.Mult: [ast.Add, ast.Div],
        ast.Div: [ast.Mult, ast.Sub],
        ast.Mod: [ast.Div, ast.Mult],
    }

    def mutate(self, node: ast.AST) -> Optional[ast.AST]:
        """Mutate arithmetic operators."""
        if isinstance(node, ast.BinOp) and type(node.op) in self.MUTATIONS:
            mutations = []
            for new_op_type in self.MUTATIONS[type(node.op)]:
                new_node = copy.deepcopy(node)
                new_node.op = new_op_type()
                mutations.append(new_node)
            return mutations[0] if mutations else None
        return None


class ComparisonOperatorMutation(MutationOperator):
    """Mutate comparison operators."""

    MUTATIONS = {
        ast.Eq: [ast.NotEq, ast.Lt, ast.Gt],
        ast.NotEq: [ast.Eq, ast.Lt, ast.Gt],
        ast.Lt: [ast.LtE, ast.Gt, ast.Eq],
        ast.LtE: [ast.Lt, ast.GtE, ast.Eq],
        ast.Gt: [ast.GtE, ast.Lt, ast.Eq],
        ast.GtE: [ast.Gt, ast.LtE, ast.Eq],
        ast.Is: [ast.IsNot, ast.Eq],
        ast.IsNot: [ast.Is, ast.NotEq],
        ast.In: [ast.NotIn],
        ast.NotIn: [ast.In],
    }

    def mutate(self, node: ast.AST) -> Optional[ast.AST]:
        """Mutate comparison operators."""
        if isinstance(node, ast.Compare) and node.ops:
            op_type = type(node.ops[0])
            if op_type in self.MUTATIONS:
                new_node = copy.deepcopy(node)
                new_op_type = self.MUTATIONS[op_type][0]
                new_node.ops = [new_op_type()]
                return new_node
        return None


class BooleanOperatorMutation(MutationOperator):
    """Mutate boolean operators."""

    MUTATIONS = {
        ast.And: ast.Or,
        ast.Or: ast.And,
    }

    def mutate(self, node: ast.AST) -> Optional[ast.AST]:
        """Mutate boolean operators."""
        if isinstance(node, ast.BoolOp) and type(node.op) in self.MUTATIONS:
            new_node = copy.deepcopy(node)
            new_node.op = self.MUTATIONS[type(node.op)]()
            return new_node
        return None


class ConstantMutation(MutationOperator):
    """Mutate constant values."""

    def mutate(self, node: ast.AST) -> Optional[ast.AST]:
        """Mutate constants."""
        if isinstance(node, ast.Constant):
            new_node = copy.deepcopy(node)
            if isinstance(node.value, bool):
                new_node.value = not node.value
            elif isinstance(node.value, int):
                new_node.value = node.value + 1 if node.value != 0 else 1
            elif isinstance(node.value, float):
                new_node.value = node.value + 1.0 if node.value != 0.0 else 1.0
            elif isinstance(node.value, str) and node.value:
                new_node.value = node.value + "_mutated"
            else:
                return None
            return new_node
        return None


class ReturnValueMutation(MutationOperator):
    """Mutate return values."""

    def mutate(self, node: ast.AST) -> Optional[ast.AST]:
        """Mutate return statements."""
        if isinstance(node, ast.Return) and node.value:
            new_node = copy.deepcopy(node)
            if isinstance(node.value, ast.Constant):
                if node.value.value is True:
                    new_node.value = ast.Constant(value=False)
                elif node.value.value is False:
                    new_node.value = ast.Constant(value=True)
                elif node.value.value is None:
                    new_node.value = ast.Constant(value=0)
                elif (
                    isinstance(node.value.value, (int, float)) and node.value.value == 0
                ):
                    new_node.value = ast.Constant(value=1)
            elif isinstance(node.value, ast.Name):
                # Replace variable returns with None
                new_node.value = ast.Constant(value=None)
            return new_node
        return None


class ConditionalMutation(MutationOperator):
    """Mutate conditional statements."""

    def mutate(self, node: ast.AST) -> Optional[ast.AST]:
        """Mutate if conditions."""
        if isinstance(node, ast.If):
            # Always true mutation
            new_node = copy.deepcopy(node)
            new_node.test = ast.Constant(value=True)
            return new_node
        return None


class MutationEngine:
    """Engine for applying mutations and running tests."""

    def __init__(
        self,
        source_dir: Path = Path("src/proof_sketcher"),
        test_dir: Path = Path("tests"),
    ):
        """Initialize mutation engine.

        Args:
            source_dir: Directory containing source code
            test_dir: Directory containing tests
        """
        self.source_dir = source_dir
        self.test_dir = test_dir
        self.operators = [
            ArithmeticOperatorMutation(),
            ComparisonOperatorMutation(),
            BooleanOperatorMutation(),
            ConstantMutation(),
            ReturnValueMutation(),
            ConditionalMutation(),
        ]

    def find_mutations(self, file_path: Path) -> List[Mutation]:
        """Find all possible mutations in a file.

        Args:
            file_path: Path to Python file

        Returns:
            List of possible mutations
        """
        mutations = []

        try:
            with open(file_path, "r") as f:
                content = f.read()
                tree = ast.parse(content)
        except Exception:
            return mutations

        # Walk the AST and find mutation points
        for node in ast.walk(tree):
            # Skip test code
            if hasattr(node, "lineno"):
                for operator in self.operators:
                    mutated = operator.mutate(node)
                    if mutated:
                        # Get original code
                        original_line = (
                            content.splitlines()[node.lineno - 1]
                            if node.lineno <= len(content.splitlines())
                            else ""
                        )

                        # Create mutation
                        mutation = Mutation(
                            file_path=file_path,
                            line_number=node.lineno,
                            original_code=original_line.strip(),
                            mutated_code=(
                                ast.unparse(mutated)
                                if hasattr(ast, "unparse")
                                else str(mutated)
                            ),
                            mutation_type=operator.__class__.__name__,
                            description=f"Mutate {type(node).__name__} at line {node.lineno}",
                        )
                        mutations.append(mutation)

        return mutations

    def apply_mutation(self, mutation: Mutation) -> str:
        """Apply a mutation to source code.

        Args:
            mutation: Mutation to apply

        Returns:
            Mutated source code
        """
        with open(mutation.file_path, "r") as f:
            lines = f.readlines()

        # Simple line replacement (more sophisticated AST-based replacement would be better)
        if mutation.line_number <= len(lines):
            # This is simplified - real implementation would properly replace AST nodes
            lines[mutation.line_number - 1] = lines[mutation.line_number - 1].replace(
                mutation.original_code, mutation.mutated_code
            )

        return "".join(lines)

    def run_tests_for_mutation(self, mutation: Mutation) -> MutationResult:
        """Run tests with a mutation applied.

        Args:
            mutation: Mutation to test

        Returns:
            MutationResult
        """
        import time

        # Create temporary file with mutation
        with tempfile.NamedTemporaryFile(
            mode="w", suffix=".py", delete=False
        ) as tmp_file:
            mutated_content = self.apply_mutation(mutation)
            tmp_file.write(mutated_content)
            tmp_path = Path(tmp_file.name)

        # Backup original file
        original_content = mutation.file_path.read_text()

        try:
            # Apply mutation
            mutation.file_path.write_text(mutated_content)

            # Run tests
            start_time = time.time()
            result = subprocess.run(
                ["python", "-m", "pytest", "-x", "--tb=short", "-q"],
                capture_output=True,
                text=True,
            )
            execution_time = time.time() - start_time

            # Check if tests caught the mutation
            killed = result.returncode != 0

            # Extract failing tests
            failing_tests = []
            if killed:
                for line in result.stdout.splitlines():
                    if "FAILED" in line:
                        failing_tests.append(line.split()[0])

            return MutationResult(
                mutation=mutation,
                killed=killed,
                test_output=result.stdout + result.stderr,
                execution_time=execution_time,
                failing_tests=failing_tests,
            )

        finally:
            # Restore original file
            mutation.file_path.write_text(original_content)
            tmp_path.unlink()

    def run_mutation_testing(
        self, target_files: Optional[List[Path]] = None, sample_rate: float = 1.0
    ) -> Dict[str, any]:
        """Run mutation testing on target files.

        Args:
            target_files: Specific files to test, or None for all
            sample_rate: Fraction of mutations to test (0.0-1.0)

        Returns:
            Dictionary of results
        """
        if target_files is None:
            target_files = list(self.source_dir.rglob("*.py"))

        all_mutations = []
        for file_path in target_files:
            if "__pycache__" not in str(file_path):
                mutations = self.find_mutations(file_path)
                all_mutations.extend(mutations)

        # Sample mutations if requested
        if sample_rate < 1.0:
            import random

            sample_size = int(len(all_mutations) * sample_rate)
            all_mutations = random.sample(all_mutations, sample_size)

        # Run tests for each mutation
        results = []
        for i, mutation in enumerate(all_mutations):
            print(f"Testing mutation {i+1}/{len(all_mutations)}: {mutation.id}")
            result = self.run_tests_for_mutation(mutation)
            results.append(result)

        # Calculate statistics
        killed_count = sum(1 for r in results if r.killed)
        survived_count = sum(1 for r in results if r.survived)

        return {
            "total_mutations": len(all_mutations),
            "killed": killed_count,
            "survived": survived_count,
            "mutation_score": killed_count / len(all_mutations) if all_mutations else 0,
            "results": results,
            "survived_mutations": [r for r in results if r.survived],
        }


class TestMutationTesting:
    """Test the mutation testing system itself."""

    def test_arithmetic_mutation(self):
        """Test arithmetic operator mutations."""
        operator = ArithmeticOperatorMutation()

        # Test addition mutation
        code = "result = a + b"
        tree = ast.parse(code)
        add_node = tree.body[0].value

        mutated = operator.mutate(add_node)
        assert mutated is not None
        assert isinstance(mutated.op, (ast.Sub, ast.Mult))

    def test_comparison_mutation(self):
        """Test comparison operator mutations."""
        operator = ComparisonOperatorMutation()

        code = "if a == b: pass"
        tree = ast.parse(code)
        compare_node = tree.body[0].test

        mutated = operator.mutate(compare_node)
        assert mutated is not None
        assert isinstance(mutated.ops[0], (ast.NotEq, ast.Lt, ast.Gt))

    def test_boolean_mutation(self):
        """Test boolean operator mutations."""
        operator = BooleanOperatorMutation()

        code = "result = a and b"
        tree = ast.parse(code)
        bool_node = tree.body[0].value

        mutated = operator.mutate(bool_node)
        assert mutated is not None
        assert isinstance(mutated.op, ast.Or)

    def test_constant_mutation(self):
        """Test constant mutations."""
        operator = ConstantMutation()

        # Test boolean mutation
        code = "flag = True"
        tree = ast.parse(code)
        const_node = tree.body[0].value

        mutated = operator.mutate(const_node)
        assert mutated is not None
        assert mutated.value is False

    def test_mutation_engine_basic(self):
        """Test basic mutation engine functionality."""
        engine = MutationEngine()

        # Create a simple test file
        test_code = """
def add(a, b):
    return a + b

def is_positive(x):
    return x > 0
"""

        with tempfile.NamedTemporaryFile(mode="w", suffix=".py", delete=False) as f:
            f.write(test_code)
            test_file = Path(f.name)

        try:
            mutations = engine.find_mutations(test_file)

            # Should find mutations for +, >, and return values
            assert len(mutations) > 0

            # Check mutation types
            mutation_types = {m.mutation_type for m in mutations}
            assert "ArithmeticOperatorMutation" in mutation_types
            assert "ComparisonOperatorMutation" in mutation_types

        finally:
            test_file.unlink()


class MutationTestReport:
    """Generate mutation testing reports."""

    @staticmethod
    def generate_report(results: Dict[str, any], output_path: Path) -> None:
        """Generate a mutation testing report.

        Args:
            results: Mutation testing results
            output_path: Path to save report
        """
        report_lines = [
            "# Mutation Testing Report",
            "=" * 80,
            "",
            f"## Summary",
            f"- Total mutations: {results['total_mutations']}",
            f"- Killed: {results['killed']} ({results['killed']/results['total_mutations']*100:.1f}%)",
            f"- Survived: {results['survived']} ({results['survived']/results['total_mutations']*100:.1f}%)",
            f"- Mutation score: {results['mutation_score']*100:.1f}%",
            "",
            "## Survived Mutations (Test Gaps)",
            "-" * 40,
        ]

        # List survived mutations
        for i, result in enumerate(results["survived_mutations"], 1):
            mutation = result.mutation
            report_lines.extend(
                [
                    f"\n### {i}. {mutation.id}",
                    f"- File: {mutation.file_path}",
                    f"- Line: {mutation.line_number}",
                    f"- Type: {mutation.mutation_type}",
                    f"- Original: `{mutation.original_code}`",
                    f"- Mutated: `{mutation.mutated_code}`",
                    f"- Description: {mutation.description}",
                ]
            )

        report_lines.extend(
            [
                "",
                "## Recommendations",
                "-" * 40,
                "Focus on adding tests for the survived mutations above.",
                "Each survived mutation represents a potential bug that tests don't catch.",
            ]
        )

        output_path.write_text("\n".join(report_lines))


def run_mutation_analysis(target_module: str = "proof_sketcher.core.utils"):
    """Run mutation analysis on a specific module.

    Args:
        target_module: Module to analyze
    """
    # Convert module to file path
    module_parts = target_module.split(".")
    file_path = Path("src") / Path(*module_parts[:-1]) / f"{module_parts[-1]}.py"

    if not file_path.exists():
        print(f"Module file not found: {file_path}")
        return

    engine = MutationEngine()
    print(f"Running mutation testing on {file_path}")

    results = engine.run_mutation_testing(
        target_files=[file_path], sample_rate=0.1  # Test 10% of mutations for speed
    )

    # Generate report
    report_path = Path(f"mutation_report_{module_parts[-1]}.md")
    MutationTestReport.generate_report(results, report_path)

    print(f"\nMutation testing complete!")
    print(f"Mutation score: {results['mutation_score']*100:.1f}%")
    print(f"Report saved to: {report_path}")

    if results["survived_mutations"]:
        print(f"\n⚠️  {len(results['survived_mutations'])} mutations survived!")
        print("These represent potential gaps in test coverage.")


if __name__ == "__main__":
    # Run mutation testing on a sample module
    run_mutation_analysis("proof_sketcher.core.utils")
