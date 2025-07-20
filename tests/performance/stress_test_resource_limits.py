#!/usr/bin/env python3
"""
Comprehensive stress test for proof-sketcher resource limits.
Tests memory, rate limiting, timeouts, file size, and batch size limits.
"""

from __future__ import annotations

import asyncio
import json
import os
import subprocess
import sys
import tempfile
import time
import traceback
from pathlib import Path

import psutil

# Add project to path
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "src"))

from proof_sketcher.core.resource_limits import (
    RateLimiter,
    RateLimitExceeded,
    ResourceLimitExceeded,
    ResourceMonitor,
    TimeoutError,
    timeout,
)
from proof_sketcher.exporter.batch_processor import BatchExporter
from proof_sketcher.generator.models import ProofSketch, ProofStrategy
from proof_sketcher.parser.lsp_client import LeanLSPClient
from proof_sketcher.parser.models import TheoremInfo
from proof_sketcher.parser.simple_parser import SimpleLeanParser


class StressTester:
    def __init__(self):
        self.results = {
            "memory_limits": {},
            "rate_limits": {},
            "timeout_limits": {},
            "file_size_limits": {},
            "batch_limits": {},
            "overall_robustness": {},
        }

    def report_result(self, category, test, status, details):
        """Record test result."""
        self.results[category][test] = {
            "status": status,
            "details": details,
            "timestamp": time.time(),
        }
        print(f"\n[{category}] {test}: {status}")
        print(f"  Details: {details}")

    async def test_memory_limits(self):
        """Test memory monitoring and enforcement."""
        print("\n=== TESTING MEMORY LIMITS ===")

        # Test 1: Memory monitor with small limit
        print("\nTest 1: Memory monitor with 50MB limit")
        monitor = ResourceMonitor(max_memory_mb=50)

        try:
            # Allocate memory gradually
            data = []
            with monitor:
                for i in range(100):
                    # Allocate ~5MB chunks
                    chunk = bytearray(5 * 1024 * 1024)
                    data.append(chunk)
                    monitor.check_memory()
                    print(f"  Allocated {(i+1)*5}MB", end="\r")

            self.report_result(
                "memory_limits",
                "basic_enforcement",
                "FAILED",
                f"No exception raised after allocating {len(data)*5}MB",
            )

        except ResourceLimitExceeded as e:
            self.report_result(
                "memory_limits",
                "basic_enforcement",
                "PASSED",
                f"Correctly caught memory limit: {e}",
            )
        except Exception as e:
            self.report_result(
                "memory_limits",
                "basic_enforcement",
                "ERROR",
                f"Unexpected error: {type(e).__name__}: {e}",
            )

        # Test 2: Async memory monitoring
        print("\nTest 2: Async memory monitoring")
        monitor = ResourceMonitor(max_memory_mb=100)

        async def memory_hog():
            data = []
            for i in range(50):
                data.append(bytearray(10 * 1024 * 1024))  # 10MB chunks
                await asyncio.sleep(0.1)
            return len(data)

        try:
            result = await monitor.monitor_async(memory_hog())
            self.report_result(
                "memory_limits",
                "async_monitoring",
                "FAILED",
                f"No exception after allocating {result*10}MB",
            )
        except ResourceLimitExceeded as e:
            self.report_result(
                "memory_limits",
                "async_monitoring",
                "PASSED",
                f"Correctly caught async memory limit: {e}",
            )
        except Exception as e:
            self.report_result(
                "memory_limits",
                "async_monitoring",
                "ERROR",
                f"Unexpected error: {type(e).__name__}: {e}",
            )

        # Test 3: Check if psutil is available
        try:
            import psutil

            self.report_result(
                "memory_limits",
                "psutil_available",
                "PASSED",
                f"psutil version {psutil.version_info}",
            )
        except ImportError:
            self.report_result(
                "memory_limits",
                "psutil_available",
                "WARNING",
                "psutil not available - memory monitoring disabled",
            )

    async def test_rate_limits(self):
        """Test rate limiting enforcement."""
        print("\n=== TESTING RATE LIMITS ===")

        # Test 1: Basic rate limiting
        print("\nTest 1: Basic rate limiting (5 calls per second)")
        limiter = RateLimiter(max_calls=5, time_window=1.0)

        calls_made = 0
        try:
            start = time.time()
            for i in range(10):
                limiter.record_call()
                calls_made += 1
                print(f"  Made call {i+1}", end="\r")

            self.report_result(
                "rate_limits",
                "basic_enforcement",
                "FAILED",
                f"Made {calls_made} calls without rate limit error",
            )

        except RateLimitExceeded as e:
            elapsed = time.time() - start
            self.report_result(
                "rate_limits",
                "basic_enforcement",
                "PASSED",
                f"Rate limit hit after {calls_made} calls in {elapsed:.2f}s: {e}",
            )
        except Exception as e:
            self.report_result(
                "rate_limits",
                "basic_enforcement",
                "ERROR",
                f"Unexpected error: {type(e).__name__}: {e}",
            )

        # Test 2: Async rate limiting with burst
        print("\nTest 2: Async rate limiting with burst")
        limiter = RateLimiter(max_calls=10, time_window=2.0)

        async def make_burst_calls():
            calls = []
            for i in range(20):
                await limiter.acquire()
                calls.append(time.time())
                print(f"  Async call {i+1}/20", end="\r")
            return calls

        try:
            start = time.time()
            call_times = await asyncio.wait_for(make_burst_calls(), timeout=5.0)
            elapsed = time.time() - start

            # Check if calls were properly rate limited
            if elapsed < 2.0:
                self.report_result(
                    "rate_limits",
                    "async_burst",
                    "FAILED",
                    f"20 calls completed in {elapsed:.2f}s (should take >2s)",
                )
            else:
                self.report_result(
                    "rate_limits",
                    "async_burst",
                    "PASSED",
                    f"Properly rate limited: 20 calls in {elapsed:.2f}s",
                )

        except asyncio.TimeoutError:
            self.report_result(
                "rate_limits",
                "async_burst",
                "WARNING",
                "Test timed out - rate limiter may be blocking indefinitely",
            )
        except Exception as e:
            self.report_result(
                "rate_limits",
                "async_burst",
                "ERROR",
                f"Unexpected error: {type(e).__name__}: {e}",
            )

        # Test 3: Context manager rate limiting
        print("\nTest 3: Context manager rate limiting")
        limiter = RateLimiter(max_calls=3, time_window=1.0)

        successes = 0
        try:
            for i in range(5):
                with limiter:
                    successes += 1
                    print(f"  Context call {i+1}", end="\r")

            self.report_result(
                "rate_limits",
                "context_manager",
                "FAILED",
                f"Made {successes} calls without rate limit",
            )

        except RateLimitExceeded as e:
            self.report_result(
                "rate_limits",
                "context_manager",
                "PASSED",
                f"Context manager rate limit after {successes} calls: {e}",
            )
        except Exception as e:
            self.report_result(
                "rate_limits",
                "context_manager",
                "ERROR",
                f"Unexpected error: {type(e).__name__}: {e}",
            )

    def test_timeout_limits(self):
        """Test timeout enforcement."""
        print("\n=== TESTING TIMEOUT LIMITS ===")

        # Test 1: Basic timeout with signal
        print("\nTest 1: Basic timeout (2 second limit)")

        def slow_operation():
            time.sleep(5)
            return "Should not reach here"

        try:
            with timeout(2):
                result = slow_operation()
            self.report_result(
                "timeout_limits",
                "basic_signal",
                "FAILED",
                f"Operation completed: {result}",
            )

        except TimeoutError as e:
            self.report_result(
                "timeout_limits", "basic_signal", "PASSED", f"Correctly timed out: {e}"
            )
        except Exception as e:
            self.report_result(
                "timeout_limits",
                "basic_signal",
                "ERROR",
                f"Unexpected error: {type(e).__name__}: {e}",
            )

        # Test 2: Nested timeouts
        print("\nTest 2: Nested timeouts")

        def nested_slow():
            with timeout(5):  # Inner timeout longer
                time.sleep(3)
                return "Inner completed"

        try:
            with timeout(1):  # Outer timeout shorter
                result = nested_slow()
            self.report_result(
                "timeout_limits",
                "nested_timeouts",
                "FAILED",
                f"Operation completed: {result}",
            )

        except TimeoutError as e:
            self.report_result(
                "timeout_limits",
                "nested_timeouts",
                "PASSED",
                f"Outer timeout triggered: {e}",
            )
        except Exception as e:
            self.report_result(
                "timeout_limits",
                "nested_timeouts",
                "ERROR",
                f"Unexpected error: {type(e).__name__}: {e}",
            )

        # Test 3: Timeout decorator
        print("\nTest 3: Timeout decorator")

        from proof_sketcher.core.resource_limits import with_timeout

        @with_timeout(1)
        def decorated_slow():
            time.sleep(2)
            return "Should timeout"

        try:
            result = decorated_slow()
            self.report_result(
                "timeout_limits",
                "decorator",
                "FAILED",
                f"Decorated function completed: {result}",
            )

        except TimeoutError as e:
            self.report_result(
                "timeout_limits",
                "decorator",
                "PASSED",
                f"Decorator timeout worked: {e}",
            )
        except Exception as e:
            self.report_result(
                "timeout_limits",
                "decorator",
                "ERROR",
                f"Unexpected error: {type(e).__name__}: {e}",
            )

    async def test_file_size_limits(self):
        """Test file size limit enforcement."""
        print("\n=== TESTING FILE SIZE LIMITS ===")

        # Create temporary directory
        with tempfile.TemporaryDirectory() as tmpdir:
            tmppath = Path(tmpdir)

            # Test 1: Simple parser with large file
            print("\nTest 1: Simple parser with 15MB file (limit is 10MB)")

            # Create a large Lean file
            large_file = tmppath / "large.lean"
            content = "-- Large file test\n\n"

            # Add theorems until file is >15MB
            theorem_template = """
theorem large_theorem_{} : ∀ (n : Nat), n + 0 = n := by
  intro n
  -- This is a very long comment to pad the file size
  -- {padding}
  rfl
"""
            padding = "x" * 1000  # 1KB of padding per theorem

            for i in range(16000):  # ~16MB
                content += theorem_template.format(i, padding=padding)

            large_file.write_text(content)
            file_size_mb = len(content) / (1024 * 1024)

            parser = SimpleLeanParser()
            try:
                # The parser checks file size in _read_file method
                result = parser.parse_file(large_file)
                self.report_result(
                    "file_size_limits",
                    "simple_parser",
                    "FAILED",
                    f"Parsed {file_size_mb:.1f}MB file without error",
                )

            except Exception as e:
                # Check if it's actually a file size error
                if "file size" in str(e).lower() or "too large" in str(e).lower():
                    self.report_result(
                        "file_size_limits",
                        "simple_parser",
                        "PASSED",
                        f"File size limit enforced: {e}",
                    )
                else:
                    self.report_result(
                        "file_size_limits",
                        "simple_parser",
                        "WARNING",
                        f"Error but not file size related: {type(e).__name__}: {e}",
                    )

            # Test 2: Check config validation
            print("\nTest 2: Parser config validation")

            from proof_sketcher.parser.config import ParserConfig

            try:
                # Try to create config with invalid file size
                config = ParserConfig(max_file_size=-1)
                self.report_result(
                    "file_size_limits",
                    "config_validation",
                    "FAILED",
                    "Accepted negative file size limit",
                )
            except ValueError as e:
                self.report_result(
                    "file_size_limits",
                    "config_validation",
                    "PASSED",
                    f"Config validation worked: {e}",
                )
            except Exception as e:
                self.report_result(
                    "file_size_limits",
                    "config_validation",
                    "ERROR",
                    f"Unexpected error: {type(e).__name__}: {e}",
                )

            # Test 3: Check actual enforcement in parser
            print("\nTest 3: File size enforcement location")

            # Create file just under limit
            under_limit_file = tmppath / "under_limit.lean"
            under_content = "theorem test : 1 = 1 := rfl\n" * 1000
            under_limit_file.write_text(under_content)

            try:
                result = parser.parse_file(under_limit_file)
                self.report_result(
                    "file_size_limits",
                    "under_limit",
                    "PASSED",
                    f"Successfully parsed file under limit ({len(under_content)/1024:.1f}KB)",
                )
            except Exception as e:
                self.report_result(
                    "file_size_limits",
                    "under_limit",
                    "FAILED",
                    f"Failed to parse file under limit: {e}",
                )

    def test_batch_limits(self):
        """Test batch processing limits."""
        print("\n=== TESTING BATCH LIMITS ===")

        # Test 1: Batch size limit enforcement
        print("\nTest 1: Batch processor with 150 theorems (limit is 100)")

        # Create 150 mock proof sketches
        sketches = []
        for i in range(150):
            # Create required fields based on the ProofSketch model
            sketch = ProofSketch(
                theorem_name=f"theorem_{i}",
                theorem_statement=f"∀ n : Nat, n + 0 = n",
                # Progressive overviews
                intuitive_overview="Adding zero doesn't change a number",
                conceptual_overview="We use induction to prove this",
                bridging_overview="We'll formalize the intuition using induction",
                formal_overview="By induction on n",
                # Key steps (required)
                key_steps=[],
                # Progressive conclusions
                intuitive_conclusion="Zero is the identity for addition",
                conceptual_conclusion="This is fundamental to arithmetic",
                bridging_conclusion="The formal proof matches our intuition",
                formal_conclusion="QED by induction",
                # Metadata
                proof_strategy=ProofStrategy.INDUCTION,
                difficulty_level="beginner",
                mathematical_areas=["arithmetic"],
            )
            sketches.append(sketch)

        with tempfile.TemporaryDirectory() as tmpdir:
            exporter = BatchExporter(output_dir=Path(tmpdir))

            # Capture warning about batch size
            import logging

            handler = logging.Handler()
            warnings = []
            handler.emit = lambda record: warnings.append(record.getMessage())
            exporter.logger.addHandler(handler)

            # Export without creating index to avoid attribute error
            results = exporter.export_multiple(sketches, create_index=False)

            # Check if batch was limited
            total_exported = sum(len(files) for files in results.values())

            if total_exported > 100 * len(results):  # 100 per format
                self.report_result(
                    "batch_limits",
                    "size_enforcement",
                    "FAILED",
                    f"Exported {total_exported} files, exceeding limit",
                )
            else:
                # Check for warning
                batch_warning = any("batch size" in w.lower() for w in warnings)
                if batch_warning:
                    self.report_result(
                        "batch_limits",
                        "size_enforcement",
                        "PASSED",
                        f"Batch limited to 100, exported {total_exported} files with warning",
                    )
                else:
                    self.report_result(
                        "batch_limits",
                        "size_enforcement",
                        "WARNING",
                        f"Batch limited but no warning issued",
                    )

        # Test 2: Check MAX_BATCH_SIZE constant
        print("\nTest 2: Verify MAX_BATCH_SIZE constant")

        if hasattr(BatchExporter, "MAX_BATCH_SIZE"):
            limit = BatchExporter.MAX_BATCH_SIZE
            self.report_result(
                "batch_limits", "constant_exists", "PASSED", f"MAX_BATCH_SIZE = {limit}"
            )
        else:
            self.report_result(
                "batch_limits",
                "constant_exists",
                "FAILED",
                "MAX_BATCH_SIZE constant not found",
            )

        # Test 3: Concurrent export limits
        print("\nTest 3: Concurrent export limits")

        if hasattr(BatchExporter, "MAX_CONCURRENT_EXPORTS"):
            limit = BatchExporter.MAX_CONCURRENT_EXPORTS
            self.report_result(
                "batch_limits",
                "concurrent_limit",
                "PASSED",
                f"MAX_CONCURRENT_EXPORTS = {limit}",
            )
        else:
            self.report_result(
                "batch_limits",
                "concurrent_limit",
                "WARNING",
                "MAX_CONCURRENT_EXPORTS constant not enforced",
            )

    async def test_lsp_client_limits(self):
        """Test LSP client resource limits."""
        print("\n=== TESTING LSP CLIENT LIMITS ===")

        # Test 1: LSP timeout
        print("\nTest 1: LSP client timeout")

        try:
            client = LeanLSPClient(
                timeout=1.0,
                max_memory_mb=100,
                rate_limit_calls=5,
                rate_limit_window=1.0,
            )

            # Create a test file
            with tempfile.NamedTemporaryFile(suffix=".lean", mode="w") as f:
                f.write("theorem test : 1 = 1 := by simp")
                f.flush()

                # Try to parse with very short timeout
                start = time.time()
                result = await client.parse_file(Path(f.name))
                elapsed = time.time() - start

                if elapsed > 1.5:
                    self.report_result(
                        "lsp_client_limits",
                        "timeout",
                        "WARNING",
                        f"Operation took {elapsed:.2f}s with 1s timeout",
                    )
                else:
                    self.report_result(
                        "lsp_client_limits",
                        "timeout",
                        "INFO",
                        f"Operation completed in {elapsed:.2f}s",
                    )

        except Exception as e:
            if "timeout" in str(e).lower():
                self.report_result(
                    "lsp_client_limits",
                    "timeout",
                    "PASSED",
                    f"LSP timeout enforced: {e}",
                )
            else:
                self.report_result(
                    "lsp_client_limits",
                    "timeout",
                    "ERROR",
                    f"Unexpected error: {type(e).__name__}: {e}",
                )

        # Test 2: LSP rate limiting
        print("\nTest 2: LSP rate limiting")

        try:
            client = LeanLSPClient(
                timeout=30.0, rate_limit_calls=3, rate_limit_window=1.0
            )

            # Make rapid requests
            with tempfile.NamedTemporaryFile(suffix=".lean", mode="w") as f:
                f.write("theorem test : 1 = 1 := rfl")
                f.flush()

                calls_made = 0
                try:
                    for i in range(5):
                        await client.parse_file(Path(f.name))
                        calls_made += 1
                        print(f"  LSP call {i+1}", end="\r")

                    self.report_result(
                        "lsp_client_limits",
                        "rate_limit",
                        "FAILED",
                        f"Made {calls_made} calls without rate limit",
                    )

                except RateLimitExceeded as e:
                    self.report_result(
                        "lsp_client_limits",
                        "rate_limit",
                        "PASSED",
                        f"LSP rate limit after {calls_made} calls: {e}",
                    )

        except Exception as e:
            self.report_result(
                "lsp_client_limits",
                "rate_limit",
                "ERROR",
                f"Unexpected error: {type(e).__name__}: {e}",
            )

    async def stress_test_all(self):
        """Run all stress tests."""
        print("=" * 60)
        print("PROOF-SKETCHER RESOURCE LIMITS STRESS TEST")
        print("=" * 60)

        # Run all tests
        await self.test_memory_limits()
        await self.test_rate_limits()
        self.test_timeout_limits()
        await self.test_file_size_limits()
        self.test_batch_limits()
        await self.test_lsp_client_limits()

        # Overall assessment
        print("\n" + "=" * 60)
        print("OVERALL ASSESSMENT")
        print("=" * 60)

        # Count results
        passed = failed = warnings = errors = 0

        for category, tests in self.results.items():
            if category == "overall_robustness":
                continue

            for test, result in tests.items():
                status = result["status"]
                if status == "PASSED":
                    passed += 1
                elif status == "FAILED":
                    failed += 1
                elif status == "WARNING":
                    warnings += 1
                elif status == "ERROR":
                    errors += 1

        total = passed + failed + warnings + errors

        print(f"\nTotal tests: {total}")
        print(f"  ✓ Passed: {passed}")
        print(f"  ✗ Failed: {failed}")
        print(f"  ⚠ Warnings: {warnings}")
        print(f"  ⚡ Errors: {errors}")

        # Robustness score
        if total > 0:
            robustness_score = (passed / total) * 100
            enforcement_score = (
                (passed / (passed + failed)) * 100 if (passed + failed) > 0 else 0
            )
        else:
            robustness_score = 0
            enforcement_score = 0

        print(f"\nRobustness Score: {robustness_score:.1f}%")
        print(f"Enforcement Score: {enforcement_score:.1f}%")

        # Detailed findings
        print("\n### DETAILED FINDINGS ###")

        findings = {
            "working_limits": [],
            "bypassed_limits": [],
            "performance_issues": [],
            "crashes": [],
            "recommendations": [],
        }

        # Analyze results
        for category, tests in self.results.items():
            if category == "overall_robustness":
                continue

            for test, result in tests.items():
                if result["status"] == "PASSED":
                    findings["working_limits"].append(
                        f"{category}.{test}: {result['details']}"
                    )
                elif result["status"] == "FAILED":
                    findings["bypassed_limits"].append(
                        f"{category}.{test}: {result['details']}"
                    )
                elif result["status"] == "WARNING":
                    findings["performance_issues"].append(
                        f"{category}.{test}: {result['details']}"
                    )
                elif result["status"] == "ERROR":
                    findings["crashes"].append(
                        f"{category}.{test}: {result['details']}"
                    )

        # Add recommendations based on findings
        if not findings["working_limits"]:
            findings["recommendations"].append(
                "CRITICAL: No resource limits are properly enforced!"
            )

        if findings["bypassed_limits"]:
            findings["recommendations"].append(
                "Fix bypassed limits to prevent resource exhaustion"
            )

        if findings["crashes"]:
            findings["recommendations"].append(
                "Address crash-causing errors for stability"
            )

        if "memory_limits.psutil_available" in str(findings["performance_issues"]):
            findings["recommendations"].append(
                "Install psutil for memory monitoring: pip install psutil"
            )

        # Print findings
        for category, items in findings.items():
            if items:
                print(f"\n{category.replace('_', ' ').title()}:")
                for item in items:
                    print(f"  - {item}")

        # Save detailed report
        report_path = Path("stress_test_report.json")
        with open(report_path, "w") as f:
            json.dump(
                {
                    "timestamp": time.time(),
                    "summary": {
                        "total_tests": total,
                        "passed": passed,
                        "failed": failed,
                        "warnings": warnings,
                        "errors": errors,
                        "robustness_score": robustness_score,
                        "enforcement_score": enforcement_score,
                    },
                    "results": self.results,
                    "findings": findings,
                },
                f,
                indent=2,
            )

        print(f"\nDetailed report saved to: {report_path}")

        # Overall verdict
        print("\n### OVERALL VERDICT ###")
        if robustness_score >= 80:
            print("✓ Resource limits are WELL IMPLEMENTED")
        elif robustness_score >= 60:
            print("⚠ Resource limits are PARTIALLY IMPLEMENTED")
        elif robustness_score >= 40:
            print("⚠ Resource limits are WEAKLY IMPLEMENTED")
        else:
            print("✗ Resource limits are POORLY IMPLEMENTED")

        return self.results


if __name__ == "__main__":
    tester = StressTester()
    asyncio.run(tester.stress_test_all())
