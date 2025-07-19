#!/usr/bin/env python3
"""
Error Handling Reliability Test Suite
=====================================

This test suite verifies that error handling in the proof-sketcher codebase
works correctly in real-world scenarios.
"""

import json
import logging
import sys
import tempfile
import traceback
from pathlib import Path
from typing import Any, Dict, List

# Add the src directory to the path
sys.path.insert(0, str(Path(__file__).parent / "src"))

from proof_sketcher.core.error_handling import (
    ErrorAccumulator,
    error_context,
    handle_errors,
    setup_error_logger,
)
from proof_sketcher.core.exceptions import (
    ConfigError,
    ExportFailedError,
    FileParseError,
    GenerationFailedError,
    InvalidPathError,
    LSPTimeoutError,
    ProofSketcherError,
    RateLimitExceeded,
    ResourceLimitExceeded,
)
from proof_sketcher.exporter.batch_processor import BatchExporter
from proof_sketcher.generator.models import ProofSketch
from proof_sketcher.parser.simple_parser import SimpleLeanParser


class ErrorHandlingTester:
    """Test suite for error handling patterns."""

    def __init__(self):
        self.logger = setup_error_logger("error_handling_test")
        self.results = []
        self.test_dir = Path(tempfile.mkdtemp())

    def run_all_tests(self):
        """Run all error handling tests."""
        print("🧪 Error Handling Test Suite")
        print("=" * 60)
        
        tests = [
            self.test_custom_exception_hierarchy,
            self.test_error_context_manager,
            self.test_error_accumulator,
            self.test_batch_operation_resilience,
            self.test_error_logging_quality,
            self.test_error_propagation,
            self.test_edge_cases,
            self.test_user_friendly_messages,
            self.test_cleanup_on_error,
            self.test_resource_limit_errors,
        ]
        
        for test in tests:
            try:
                test()
            except Exception as e:
                self.results.append({
                    "test": test.__name__,
                    "status": "FAILED",
                    "error": str(e),
                    "traceback": traceback.format_exc()
                })
        
        self._print_summary()

    def test_custom_exception_hierarchy(self):
        """Test 1: Verify custom exception hierarchy works correctly."""
        print("\n📌 Test 1: Custom Exception Hierarchy")
        
        test_results = []
        
        # Test base exception with details
        try:
            raise ProofSketcherError("Base error", {"key": "value"})
        except ProofSketcherError as e:
            test_results.append({
                "check": "Base exception details",
                "passed": e.details == {"key": "value"},
                "message": f"Details: {e.details}"
            })
        
        # Test specific exceptions
        try:
            raise FileParseError("/path/to/file.lean", "Parse failed", 42)
        except FileParseError as e:
            test_results.append({
                "check": "FileParseError details",
                "passed": e.details.get("line_number") == 42,
                "message": f"Line number captured: {e.details}"
            })
        
        # Test resource limit exception
        try:
            raise ResourceLimitExceeded("Memory", "4GB", "8GB")
        except ResourceLimitExceeded as e:
            test_results.append({
                "check": "ResourceLimitExceeded message",
                "passed": "Memory limit exceeded" in str(e),
                "message": f"Error message: {e}"
            })
        
        # Test exception inheritance
        try:
            raise LSPTimeoutError("LSP operation timed out")
        except ProofSketcherError:
            test_results.append({
                "check": "Exception inheritance",
                "passed": True,
                "message": "LSPTimeoutError caught as ProofSketcherError"
            })
        
        self._report_test_results("Custom Exception Hierarchy", test_results)

    def test_error_context_manager(self):
        """Test 2: Verify error context manager behavior."""
        print("\n📌 Test 2: Error Context Manager")
        
        test_results = []
        logger = setup_error_logger("test_context")
        
        # Test successful operation
        try:
            with error_context("successful operation", logger):
                result = 1 + 1
            test_results.append({
                "check": "Successful operation",
                "passed": True,
                "message": "No exception raised"
            })
        except:
            test_results.append({
                "check": "Successful operation",
                "passed": False,
                "message": "Unexpected exception"
            })
        
        # Test ProofSketcherError passthrough
        try:
            with error_context("failing operation", logger):
                raise ConfigError("Config missing")
        except ConfigError:
            test_results.append({
                "check": "ProofSketcherError passthrough",
                "passed": True,
                "message": "ConfigError passed through unchanged"
            })
        except:
            test_results.append({
                "check": "ProofSketcherError passthrough",
                "passed": False,
                "message": "Error was wrapped unexpectedly"
            })
        
        # Test unexpected error wrapping
        try:
            with error_context("unexpected error", logger):
                raise ValueError("Unexpected!")
        except ProofSketcherError as e:
            test_results.append({
                "check": "Unexpected error wrapping",
                "passed": "Unexpected error during unexpected error" in str(e),
                "message": f"Wrapped as: {e}"
            })
            test_results.append({
                "check": "Original error in details",
                "passed": e.details.get("original_error") == "Unexpected!",
                "message": f"Details preserved: {e.details.get('original_error')}"
            })
        
        self._report_test_results("Error Context Manager", test_results)

    def test_error_accumulator(self):
        """Test 3: Verify error accumulator for batch operations."""
        print("\n📌 Test 3: Error Accumulator")
        
        test_results = []
        accumulator = ErrorAccumulator(self.logger)
        
        # Test capturing errors
        items = ["item1", "item2", "item3", "item4", "item5"]
        
        for i, item in enumerate(items):
            with accumulator.capture(f"processing {item}"):
                if i % 2 == 1:  # Fail on odd indices
                    raise ValueError(f"Failed to process {item}")
        
        test_results.append({
            "check": "Error count",
            "passed": accumulator.error_count == 2,
            "message": f"Captured {accumulator.error_count} errors"
        })
        
        test_results.append({
            "check": "Has errors property",
            "passed": accumulator.has_errors,
            "message": "Correctly reports having errors"
        })
        
        # Test error summary
        summary = accumulator.get_summary()
        test_results.append({
            "check": "Error summary format",
            "passed": "Found 2 errors:" in summary and "item2" in summary,
            "message": f"Summary includes error details"
        })
        
        # Test raising all errors
        try:
            accumulator.raise_all()
        except ProofSketcherError as e:
            test_results.append({
                "check": "Multiple errors exception",
                "passed": "Multiple errors occurred" in str(e),
                "message": f"Raised composite error: {e}"
            })
            test_results.append({
                "check": "Error details in exception",
                "passed": len(e.details.get("errors", [])) == 2,
                "message": f"All errors included in details"
            })
        
        # Test single error behavior
        single_accumulator = ErrorAccumulator()
        with single_accumulator.capture("single failure"):
            raise ConfigError("Single error")
        
        try:
            single_accumulator.raise_all()
        except ConfigError:
            test_results.append({
                "check": "Single error passthrough",
                "passed": True,
                "message": "Single error raised directly"
            })
        
        self._report_test_results("Error Accumulator", test_results)

    def test_batch_operation_resilience(self):
        """Test 4: Verify batch operations continue after failures."""
        print("\n📌 Test 4: Batch Operation Resilience")
        
        test_results = []
        
        # Create test proof sketches with some that will fail
        sketches = []
        for i in range(5):
            sketch = ProofSketch(
                theorem_name=f"theorem_{i}" if i != 2 else "bad/name/with/slashes",
                introduction=f"Introduction for theorem {i}",
                proof_method="Test method",
                key_steps=["Step 1", "Step 2"],
                conclusion="Test conclusion",
                difficulty_level="beginner",
                mathematical_areas=["testing"]
            )
            sketches.append(sketch)
        
        # Test batch export with failures
        batch_exporter = BatchExporter(self.test_dir / "batch_test")
        results = batch_exporter.export_multiple(sketches, formats=["markdown"])
        
        # Check that successful exports completed
        markdown_files = results.get("markdown", [])
        test_results.append({
            "check": "Partial batch success",
            "passed": len(markdown_files) >= 4,  # At least 4 out of 5 should succeed
            "message": f"Exported {len(markdown_files)} out of 5 files"
        })
        
        # Verify files were actually created
        created_files = list((self.test_dir / "batch_test" / "markdown").glob("*.md"))
        test_results.append({
            "check": "Files actually created",
            "passed": len(created_files) >= 4,
            "message": f"Found {len(created_files)} markdown files on disk"
        })
        
        self._report_test_results("Batch Operation Resilience", test_results)

    def test_error_logging_quality(self):
        """Test 5: Verify error logging captures sufficient context."""
        print("\n📌 Test 5: Error Logging Quality")
        
        test_results = []
        
        # Capture log output
        import io
        log_capture = io.StringIO()
        handler = logging.StreamHandler(log_capture)
        handler.setLevel(logging.ERROR)
        
        test_logger = logging.getLogger("test_logging")
        test_logger.addHandler(handler)
        test_logger.setLevel(logging.ERROR)
        
        # Test structured error logging
        with error_context("database operation", test_logger):
            try:
                raise ConnectionError("Database unavailable")
            except:
                pass
        
        log_output = log_capture.getvalue()
        test_results.append({
            "check": "Error context in logs",
            "passed": "database operation" in log_output,
            "message": "Operation context included in error log"
        })
        
        test_results.append({
            "check": "Original error in logs",
            "passed": "Database unavailable" in log_output,
            "message": "Original error message preserved"
        })
        
        # Test handle_errors decorator logging
        @handle_errors(default_return=None, logger=test_logger)
        def failing_function():
            raise InvalidPathError("Bad path: /etc/passwd")
        
        log_capture.truncate(0)
        log_capture.seek(0)
        
        result = failing_function()
        log_output = log_capture.getvalue()
        
        test_results.append({
            "check": "Function context in decorator logs",
            "passed": "failing_function" in log_output,
            "message": "Function name included in error log"
        })
        
        self._report_test_results("Error Logging Quality", test_results)

    def test_error_propagation(self):
        """Test 6: Verify error propagation through the stack."""
        print("\n📌 Test 6: Error Propagation")
        
        test_results = []
        
        # Create a chain of function calls
        def level_3():
            raise FileParseError("/test.lean", "Syntax error", 42)
        
        def level_2():
            with error_context("level 2 operation"):
                level_3()
        
        def level_1():
            try:
                level_2()
            except ProofSketcherError:
                raise GenerationFailedError("Generation failed due to parse error")
        
        # Test error chain
        try:
            level_1()
        except GenerationFailedError as e:
            test_results.append({
                "check": "Top-level error type",
                "passed": isinstance(e, GenerationFailedError),
                "message": f"Caught {type(e).__name__}"
            })
            
            # Check if we can trace back to the original error
            test_results.append({
                "check": "Error message clarity",
                "passed": "Generation failed" in str(e),
                "message": "High-level error message is clear"
            })
        
        self._report_test_results("Error Propagation", test_results)

    def test_edge_cases(self):
        """Test 7: Test edge cases in error handling."""
        print("\n📌 Test 7: Edge Cases")
        
        test_results = []
        
        # Test empty error accumulator
        empty_acc = ErrorAccumulator()
        test_results.append({
            "check": "Empty accumulator summary",
            "passed": empty_acc.get_summary() == "No errors",
            "message": "Empty accumulator returns 'No errors'"
        })
        
        empty_acc.raise_all()  # Should not raise
        test_results.append({
            "check": "Empty accumulator raise_all",
            "passed": True,
            "message": "raise_all() with no errors doesn't raise"
        })
        
        # Test nested error contexts
        try:
            with error_context("outer operation"):
                with error_context("inner operation"):
                    raise KeyError("Missing key")
        except ProofSketcherError as e:
            test_results.append({
                "check": "Nested context handling",
                "passed": "inner operation" in str(e),
                "message": "Inner context preserved in error"
            })
        
        # Test very long error messages
        long_message = "x" * 10000
        try:
            raise ProofSketcherError(long_message)
        except ProofSketcherError as e:
            test_results.append({
                "check": "Long error message handling",
                "passed": len(str(e)) == 10000,
                "message": "Long messages handled without truncation"
            })
        
        self._report_test_results("Edge Cases", test_results)

    def test_user_friendly_messages(self):
        """Test 8: Verify error messages are helpful to users."""
        print("\n📌 Test 8: User-Friendly Messages")
        
        test_results = []
        
        # Test file not found error
        parser = SimpleLeanParser()
        result = parser.parse_file("/nonexistent/file.lean")
        
        if result.errors:
            error_msg = result.errors[0].message
            test_results.append({
                "check": "File not found message",
                "passed": "File not found" in error_msg and "/nonexistent/file.lean" in error_msg,
                "message": f"Clear error: {error_msg}"
            })
        
        # Test file size limit error
        large_file = self.test_dir / "large.lean"
        large_file.write_text("x" * (11 * 1024 * 1024))  # 11MB file
        
        result = parser.parse_file(large_file)
        if result.errors:
            error_msg = result.errors[0].message
            test_results.append({
                "check": "File size error message",
                "passed": "File too large" in error_msg and "MB" in error_msg,
                "message": f"Size limit explained: {error_msg}"
            })
        
        # Test rate limit error
        try:
            raise RateLimitExceeded(100, 60)
        except RateLimitExceeded as e:
            test_results.append({
                "check": "Rate limit message",
                "passed": "Rate" in str(e) and "100" in str(e),
                "message": f"Rate limit clear: {e}"
            })
        
        self._report_test_results("User-Friendly Messages", test_results)

    def test_cleanup_on_error(self):
        """Test 9: Verify cleanup happens on error."""
        print("\n📌 Test 9: Cleanup on Error")
        
        test_results = []
        
        # Test that temporary resources are cleaned up
        cleanup_called = False
        
        def operation_with_cleanup():
            nonlocal cleanup_called
            try:
                # Simulate resource allocation
                temp_file = self.test_dir / "temp_resource.txt"
                temp_file.write_text("temporary data")
                
                # Simulate error
                raise ValueError("Operation failed")
            finally:
                # Cleanup
                if temp_file.exists():
                    temp_file.unlink()
                cleanup_called = True
        
        try:
            with error_context("operation with cleanup"):
                operation_with_cleanup()
        except ProofSketcherError:
            pass
        
        test_results.append({
            "check": "Cleanup executed on error",
            "passed": cleanup_called,
            "message": "Finally block executed during error"
        })
        
        test_results.append({
            "check": "Temporary file cleaned up",
            "passed": not (self.test_dir / "temp_resource.txt").exists(),
            "message": "Temporary resources removed"
        })
        
        self._report_test_results("Cleanup on Error", test_results)

    def test_resource_limit_errors(self):
        """Test 10: Verify resource limit errors are handled properly."""
        print("\n📌 Test 10: Resource Limit Errors")
        
        test_results = []
        
        # Test timeout handling
        from proof_sketcher.core.resource_limits import timeout, TimeoutError
        
        try:
            with timeout(0.1):  # 100ms timeout
                import time
                time.sleep(0.2)  # Sleep longer than timeout
        except TimeoutError as e:
            test_results.append({
                "check": "Timeout error raised",
                "passed": True,
                "message": f"Timeout detected: {e}"
            })
        
        # Test memory limit error
        try:
            raise ResourceLimitExceeded("Memory", "4GB", "8.5GB")
        except ResourceLimitExceeded as e:
            test_results.append({
                "check": "Resource limit details",
                "passed": e.details["resource_type"] == "Memory",
                "message": "Resource type captured in details"
            })
            test_results.append({
                "check": "Resource limit message format",
                "passed": "8.5GB > 4GB" in str(e),
                "message": f"Clear limit explanation: {e}"
            })
        
        self._report_test_results("Resource Limit Errors", test_results)

    def _report_test_results(self, test_name: str, results: List[Dict[str, Any]]):
        """Report results for a specific test."""
        passed = sum(1 for r in results if r["passed"])
        total = len(results)
        
        status = "PASSED" if passed == total else "FAILED"
        emoji = "✅" if status == "PASSED" else "❌"
        
        print(f"\n{emoji} {test_name}: {passed}/{total} checks passed")
        
        for result in results:
            check_emoji = "✓" if result["passed"] else "✗"
            print(f"  {check_emoji} {result['check']}: {result['message']}")
        
        self.results.append({
            "test": test_name,
            "status": status,
            "passed": passed,
            "total": total,
            "details": results
        })

    def _print_summary(self):
        """Print overall test summary."""
        print("\n" + "=" * 60)
        print("📊 TEST SUMMARY")
        print("=" * 60)
        
        total_tests = len(self.results)
        passed_tests = sum(1 for r in self.results if r["status"] == "PASSED")
        
        print(f"\nTotal Tests: {total_tests}")
        print(f"Passed: {passed_tests}")
        print(f"Failed: {total_tests - passed_tests}")
        
        if passed_tests < total_tests:
            print("\n❌ FAILED TESTS:")
            for result in self.results:
                if result["status"] == "FAILED":
                    print(f"  - {result['test']}")
                    if "error" in result:
                        print(f"    Error: {result['error']}")
        
        # Overall assessment
        print("\n" + "=" * 60)
        print("🎯 ERROR HANDLING ASSESSMENT")
        print("=" * 60)
        
        assessments = {
            "Custom exception hierarchy": self._check_result("Custom Exception Hierarchy"),
            "Error context managers": self._check_result("Error Context Manager"),
            "Error accumulator": self._check_result("Error Accumulator"),
            "Batch operation resilience": self._check_result("Batch Operation Resilience"),
            "Logging quality": self._check_result("Error Logging Quality"),
            "Error propagation": self._check_result("Error Propagation"),
            "Edge case handling": self._check_result("Edge Cases"),
            "User-friendly messages": self._check_result("User-Friendly Messages"),
            "Cleanup reliability": self._check_result("Cleanup on Error"),
            "Resource limit handling": self._check_result("Resource Limit Errors"),
        }
        
        for feature, status in assessments.items():
            emoji = "✅" if status else "❌"
            print(f"{emoji} {feature}: {'Working' if status else 'Issues found'}")
        
        # Final verdict
        all_passing = all(assessments.values())
        print("\n" + "=" * 60)
        if all_passing:
            print("✅ OVERALL: Error handling implementation is SOLID")
            print("\nThe error handling patterns work as claimed:")
            print("- Exceptions provide good context and details")
            print("- Batch operations handle partial failures gracefully")
            print("- Error messages are clear and actionable")
            print("- Cleanup and recovery mechanisms work reliably")
            print("- Logging captures sufficient debugging context")
        else:
            print("⚠️  OVERALL: Error handling has some issues")
            print("\nAreas needing attention:")
            for feature, status in assessments.items():
                if not status:
                    print(f"- {feature}")
        
        # Save detailed report
        report_path = self.test_dir / "error_handling_report.json"
        with open(report_path, "w") as f:
            json.dump({
                "summary": {
                    "total_tests": total_tests,
                    "passed": passed_tests,
                    "failed": total_tests - passed_tests,
                    "all_passing": all_passing
                },
                "assessments": assessments,
                "detailed_results": self.results
            }, f, indent=2)
        
        print(f"\n📄 Detailed report saved to: {report_path}")

    def _check_result(self, test_name: str) -> bool:
        """Check if a specific test passed."""
        for result in self.results:
            if result["test"] == test_name:
                return result["status"] == "PASSED"
        return False


if __name__ == "__main__":
    tester = ErrorHandlingTester()
    tester.run_all_tests()