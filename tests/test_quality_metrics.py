"""Test quality metrics and reporting system.

This module provides comprehensive test quality metrics including:
- Test coverage analysis
- Test execution time tracking
- Assertion density metrics
- Mock usage analysis
- Test complexity metrics
- Mutation testing integration
"""

import ast
import json
import time
from collections import defaultdict
from dataclasses import dataclass, field
from pathlib import Path
from typing import Dict, List, Optional, Set, Tuple

import pytest
from coverage import Coverage


@dataclass
class TestMetrics:
    """Metrics for a single test."""
    
    name: str
    file: str
    execution_time: float
    assertion_count: int
    mock_count: int
    lines_of_code: int
    complexity: int
    passed: bool
    coverage_percentage: float = 0.0
    
    @property
    def assertion_density(self) -> float:
        """Calculate assertion density (assertions per line)."""
        return self.assertion_count / self.lines_of_code if self.lines_of_code > 0 else 0.0
    
    @property
    def quality_score(self) -> float:
        """Calculate overall quality score (0-100)."""
        scores = []
        
        # Assertion density score (0-25)
        density_score = min(self.assertion_density * 50, 25)
        scores.append(density_score)
        
        # Coverage score (0-25)
        coverage_score = self.coverage_percentage * 0.25
        scores.append(coverage_score)
        
        # Complexity score (0-25) - lower is better
        complexity_score = max(25 - self.complexity, 0)
        scores.append(complexity_score)
        
        # Mock usage score (0-25) - moderate mocking is good
        if self.mock_count == 0:
            mock_score = 15  # Some mocking expected
        elif self.mock_count <= 5:
            mock_score = 25  # Good balance
        else:
            mock_score = max(25 - (self.mock_count - 5) * 2, 0)
        scores.append(mock_score)
        
        return sum(scores)


@dataclass
class FileMetrics:
    """Metrics for a test file."""
    
    file_path: Path
    test_count: int = 0
    total_assertions: int = 0
    total_mocks: int = 0
    total_lines: int = 0
    tests: List[TestMetrics] = field(default_factory=list)
    coverage_data: Optional[Dict] = None
    
    @property
    def average_assertion_density(self) -> float:
        """Average assertion density across all tests."""
        if not self.tests:
            return 0.0
        return sum(t.assertion_density for t in self.tests) / len(self.tests)
    
    @property
    def average_quality_score(self) -> float:
        """Average quality score across all tests."""
        if not self.tests:
            return 0.0
        return sum(t.quality_score for t in self.tests) / len(self.tests)
    
    @property
    def pass_rate(self) -> float:
        """Percentage of tests that passed."""
        if not self.tests:
            return 0.0
        passed = sum(1 for t in self.tests if t.passed)
        return (passed / len(self.tests)) * 100


@dataclass
class ProjectMetrics:
    """Metrics for the entire test suite."""
    
    total_files: int = 0
    total_tests: int = 0
    total_assertions: int = 0
    total_mocks: int = 0
    total_lines: int = 0
    execution_time: float = 0.0
    coverage_percentage: float = 0.0
    files: Dict[str, FileMetrics] = field(default_factory=dict)
    
    @property
    def average_assertion_density(self) -> float:
        """Average assertion density across all tests."""
        if self.total_lines == 0:
            return 0.0
        return self.total_assertions / self.total_lines
    
    @property
    def average_quality_score(self) -> float:
        """Average quality score across all files."""
        if not self.files:
            return 0.0
        return sum(f.average_quality_score for f in self.files.values()) / len(self.files)
    
    @property
    def test_distribution(self) -> Dict[str, int]:
        """Distribution of tests by quality score ranges."""
        distribution = defaultdict(int)
        for file_metrics in self.files.values():
            for test in file_metrics.tests:
                score = test.quality_score
                if score >= 90:
                    distribution["Excellent (90-100)"] += 1
                elif score >= 70:
                    distribution["Good (70-89)"] += 1
                elif score >= 50:
                    distribution["Fair (50-69)"] += 1
                else:
                    distribution["Poor (0-49)"] += 1
        return dict(distribution)


class TestQualityAnalyzer:
    """Analyzer for test quality metrics."""
    
    def __init__(self, test_dir: Path = Path("tests")):
        """Initialize the analyzer.
        
        Args:
            test_dir: Directory containing test files
        """
        self.test_dir = test_dir
        self.metrics = ProjectMetrics()
    
    def analyze_test_file(self, file_path: Path) -> FileMetrics:
        """Analyze a single test file.
        
        Args:
            file_path: Path to the test file
            
        Returns:
            FileMetrics for the file
        """
        file_metrics = FileMetrics(file_path=file_path)
        
        try:
            with open(file_path, 'r') as f:
                content = f.read()
                tree = ast.parse(content)
            
            # Count lines
            file_metrics.total_lines = len(content.splitlines())
            
            # Find test functions and analyze them
            for node in ast.walk(tree):
                if isinstance(node, ast.FunctionDef) and node.name.startswith("test_"):
                    test_metrics = self._analyze_test_function(node, file_path.name)
                    file_metrics.tests.append(test_metrics)
                    file_metrics.test_count += 1
                    file_metrics.total_assertions += test_metrics.assertion_count
                    file_metrics.total_mocks += test_metrics.mock_count
            
        except Exception as e:
            print(f"Error analyzing {file_path}: {e}")
        
        return file_metrics
    
    def _analyze_test_function(self, node: ast.FunctionDef, filename: str) -> TestMetrics:
        """Analyze a single test function.
        
        Args:
            node: AST node for the function
            filename: Name of the file containing the test
            
        Returns:
            TestMetrics for the function
        """
        metrics = TestMetrics(
            name=node.name,
            file=filename,
            execution_time=0.0,  # Will be set during execution
            assertion_count=0,
            mock_count=0,
            lines_of_code=node.end_lineno - node.lineno + 1 if node.end_lineno else 1,
            complexity=self._calculate_complexity(node),
            passed=True  # Will be updated based on test results
        )
        
        # Count assertions and mocks
        for child in ast.walk(node):
            if isinstance(child, ast.Assert):
                metrics.assertion_count += 1
            elif isinstance(child, ast.Call):
                if hasattr(child.func, 'id') and child.func.id == 'assert':
                    metrics.assertion_count += 1
                elif hasattr(child.func, 'attr'):
                    if child.func.attr.startswith('assert'):
                        metrics.assertion_count += 1
                    elif 'mock' in child.func.attr.lower():
                        metrics.mock_count += 1
            elif isinstance(child, ast.Name):
                if 'mock' in child.id.lower():
                    metrics.mock_count += 1
        
        return metrics
    
    def _calculate_complexity(self, node: ast.FunctionDef) -> int:
        """Calculate cyclomatic complexity of a function.
        
        Args:
            node: AST node for the function
            
        Returns:
            Complexity score
        """
        complexity = 1  # Base complexity
        
        for child in ast.walk(node):
            if isinstance(child, (ast.If, ast.While, ast.For)):
                complexity += 1
            elif isinstance(child, ast.ExceptHandler):
                complexity += 1
            elif isinstance(child, ast.BoolOp):
                complexity += len(child.values) - 1
        
        return complexity
    
    def analyze_project(self) -> ProjectMetrics:
        """Analyze all test files in the project.
        
        Returns:
            ProjectMetrics for the entire test suite
        """
        test_files = list(self.test_dir.rglob("test_*.py"))
        
        for file_path in test_files:
            if "__pycache__" not in str(file_path):
                file_metrics = self.analyze_test_file(file_path)
                self.metrics.files[str(file_path)] = file_metrics
                self.metrics.total_files += 1
                self.metrics.total_tests += file_metrics.test_count
                self.metrics.total_assertions += file_metrics.total_assertions
                self.metrics.total_mocks += file_metrics.total_mocks
                self.metrics.total_lines += file_metrics.total_lines
        
        return self.metrics
    
    def generate_report(self, output_path: Optional[Path] = None) -> str:
        """Generate a comprehensive test quality report.
        
        Args:
            output_path: Optional path to save the report
            
        Returns:
            Report as a string
        """
        report_lines = [
            "# Test Quality Report",
            "=" * 80,
            "",
            f"## Summary",
            f"- Total test files: {self.metrics.total_files}",
            f"- Total tests: {self.metrics.total_tests}",
            f"- Total assertions: {self.metrics.total_assertions}",
            f"- Total lines of test code: {self.metrics.total_lines}",
            f"- Coverage: {self.metrics.coverage_percentage:.1f}%",
            f"- Average assertion density: {self.metrics.average_assertion_density:.3f}",
            f"- Average quality score: {self.metrics.average_quality_score:.1f}/100",
            "",
            "## Test Distribution by Quality",
        ]
        
        for category, count in sorted(self.metrics.test_distribution.items(), reverse=True):
            percentage = (count / self.metrics.total_tests * 100) if self.metrics.total_tests > 0 else 0
            report_lines.append(f"- {category}: {count} ({percentage:.1f}%)")
        
        report_lines.extend([
            "",
            "## Top Quality Tests",
            "-" * 40,
        ])
        
        # Find top quality tests
        all_tests = []
        for file_metrics in self.metrics.files.values():
            all_tests.extend(file_metrics.tests)
        
        top_tests = sorted(all_tests, key=lambda t: t.quality_score, reverse=True)[:10]
        
        for i, test in enumerate(top_tests, 1):
            report_lines.append(
                f"{i}. {test.name} ({test.file}) - Score: {test.quality_score:.1f}"
            )
        
        report_lines.extend([
            "",
            "## Tests Needing Improvement",
            "-" * 40,
        ])
        
        # Find low quality tests
        low_tests = sorted(all_tests, key=lambda t: t.quality_score)[:10]
        
        for i, test in enumerate(low_tests, 1):
            issues = []
            if test.assertion_density < 0.1:
                issues.append("low assertion density")
            if test.mock_count > 10:
                issues.append("excessive mocking")
            if test.complexity > 10:
                issues.append("high complexity")
            
            report_lines.append(
                f"{i}. {test.name} ({test.file}) - Score: {test.quality_score:.1f} "
                f"Issues: {', '.join(issues) if issues else 'general quality'}"
            )
        
        report_lines.extend([
            "",
            "## File-Level Metrics",
            "-" * 40,
        ])
        
        # Sort files by average quality score
        sorted_files = sorted(
            self.metrics.files.items(),
            key=lambda x: x[1].average_quality_score,
            reverse=True
        )
        
        for file_path, file_metrics in sorted_files[:20]:  # Top 20 files
            report_lines.append(
                f"- {Path(file_path).name}: "
                f"{file_metrics.test_count} tests, "
                f"avg score: {file_metrics.average_quality_score:.1f}, "
                f"pass rate: {file_metrics.pass_rate:.1f}%"
            )
        
        report = "\n".join(report_lines)
        
        if output_path:
            output_path.write_text(report)
        
        return report
    
    def export_metrics_json(self, output_path: Path) -> None:
        """Export metrics as JSON for further analysis.
        
        Args:
            output_path: Path to save the JSON file
        """
        metrics_dict = {
            "summary": {
                "total_files": self.metrics.total_files,
                "total_tests": self.metrics.total_tests,
                "total_assertions": self.metrics.total_assertions,
                "total_lines": self.metrics.total_lines,
                "coverage_percentage": self.metrics.coverage_percentage,
                "average_assertion_density": self.metrics.average_assertion_density,
                "average_quality_score": self.metrics.average_quality_score,
                "test_distribution": self.metrics.test_distribution
            },
            "files": {}
        }
        
        for file_path, file_metrics in self.metrics.files.items():
            metrics_dict["files"][file_path] = {
                "test_count": file_metrics.test_count,
                "average_quality_score": file_metrics.average_quality_score,
                "pass_rate": file_metrics.pass_rate,
                "tests": [
                    {
                        "name": test.name,
                        "quality_score": test.quality_score,
                        "assertion_density": test.assertion_density,
                        "complexity": test.complexity,
                        "mock_count": test.mock_count
                    }
                    for test in file_metrics.tests
                ]
            }
        
        with open(output_path, 'w') as f:
            json.dump(metrics_dict, f, indent=2)


class CoverageAnalyzer:
    """Analyzer for test coverage metrics."""
    
    def __init__(self, source_dir: Path = Path("src/proof_sketcher")):
        """Initialize the coverage analyzer.
        
        Args:
            source_dir: Directory containing source code
        """
        self.source_dir = source_dir
        self.cov = Coverage(source=[str(source_dir)])
    
    def analyze_coverage(self) -> Dict[str, float]:
        """Analyze test coverage.
        
        Returns:
            Dictionary of coverage metrics
        """
        self.cov.start()
        
        # Run pytest programmatically
        pytest.main(["-x", "--tb=no", "-q"])
        
        self.cov.stop()
        self.cov.save()
        
        # Get coverage data
        total_coverage = self.cov.report(show_missing=False)
        
        # Get per-file coverage
        file_coverage = {}
        for filename in self.cov.get_data().measured_files():
            if str(self.source_dir) in filename:
                analysis = self.cov.analysis2(filename)
                if analysis:
                    executed = len(analysis[1])
                    missing = len(analysis[3])
                    total = executed + missing
                    if total > 0:
                        coverage_pct = (executed / total) * 100
                        file_coverage[filename] = coverage_pct
        
        return {
            "total_coverage": total_coverage,
            "file_coverage": file_coverage,
            "uncovered_files": [f for f, cov in file_coverage.items() if cov < 80]
        }


# Pytest plugin for collecting metrics during test execution
class MetricsPlugin:
    """Pytest plugin for collecting test execution metrics."""
    
    def __init__(self):
        self.test_metrics = {}
        self.start_times = {}
    
    def pytest_runtest_setup(self, item):
        """Called before each test runs."""
        self.start_times[item.nodeid] = time.time()
    
    def pytest_runtest_makereport(self, item, call):
        """Called after each test phase."""
        if call.when == "call":
            duration = time.time() - self.start_times.get(item.nodeid, time.time())
            self.test_metrics[item.nodeid] = {
                "duration": duration,
                "outcome": call.excinfo is None
            }


def pytest_configure(config):
    """Register the metrics plugin."""
    config._metrics = MetricsPlugin()
    config.pluginmanager.register(config._metrics)


def generate_quality_report():
    """Generate a comprehensive test quality report."""
    # Analyze test quality
    analyzer = TestQualityAnalyzer()
    metrics = analyzer.analyze_project()
    
    # Analyze coverage
    coverage_analyzer = CoverageAnalyzer()
    coverage_data = coverage_analyzer.analyze_coverage()
    
    # Update metrics with coverage data
    metrics.coverage_percentage = coverage_data["total_coverage"]
    
    # Generate reports
    report_path = Path("test_quality_report.md")
    analyzer.generate_report(report_path)
    
    json_path = Path("test_metrics.json")
    analyzer.export_metrics_json(json_path)
    
    print(f"Test quality report generated: {report_path}")
    print(f"Metrics exported to: {json_path}")
    print(f"\nSummary:")
    print(f"- Total coverage: {metrics.coverage_percentage:.1f}%")
    print(f"- Average quality score: {metrics.average_quality_score:.1f}/100")
    print(f"- Test distribution: {metrics.test_distribution}")


if __name__ == "__main__":
    generate_quality_report()