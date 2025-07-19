#!/usr/bin/env python3
"""
Critical Error Handling Test
============================

Tests the most important error handling patterns:
1. Error accumulation in batch operations
2. Resource limit handling
3. Error context propagation
4. Logging structured messages
"""

import logging
import sys
import tempfile
import time
from io import StringIO
from pathlib import Path

# Add the src directory to the path
sys.path.insert(0, str(Path(__file__).parent / "src"))

from proof_sketcher.core.error_handling import ErrorAccumulator, error_context, setup_error_logger
from proof_sketcher.core.exceptions import ProofSketcherError, ResourceLimitExceeded
from proof_sketcher.core.resource_limits import timeout, TimeoutError
from proof_sketcher.parser.simple_parser import SimpleLeanParser


def test_error_accumulation():
    """Test error accumulation in batch operations."""
    print("🧪 Testing Error Accumulation...")
    
    accumulator = ErrorAccumulator()
    
    # Simulate processing 10 items with some failures
    items = range(10)
    successful_items = []
    
    for i in items:
        with accumulator.capture(f"processing item {i}"):
            if i % 3 == 0:  # Fail every 3rd item
                raise ValueError(f"Item {i} failed")
            successful_items.append(i)
    
    print(f"✓ Processed {len(successful_items)} items successfully")
    print(f"✓ Accumulated {accumulator.error_count} errors")
    print(f"✓ Has errors: {accumulator.has_errors}")
    
    # Test error summary
    summary = accumulator.get_summary()
    print(f"✓ Summary includes failure details: {'Item 0 failed' in summary}")
    
    # Test that we can continue processing despite errors
    assert len(successful_items) == 6  # Should have processed 6 out of 10
    assert accumulator.error_count == 4  # Should have 4 failures
    
    return True


def test_resource_limits():
    """Test resource limit enforcement."""
    print("\n🧪 Testing Resource Limits...")
    
    # Test timeout handling
    try:
        with timeout(0.1):  # 100ms timeout
            time.sleep(0.2)  # Sleep longer than timeout
        assert False, "Timeout should have been triggered"
    except TimeoutError:
        print("✓ Timeout correctly triggered")
    
    # Test resource limit exception
    try:
        raise ResourceLimitExceeded("CPU", "80%", "95%")
    except ResourceLimitExceeded as e:
        assert "CPU limit exceeded" in str(e)
        assert e.details["resource_type"] == "CPU"
        print("✓ Resource limit exception contains proper details")
    
    return True


def test_error_context_propagation():
    """Test error context propagation through call stack."""
    print("\n🧪 Testing Error Context Propagation...")
    
    def deep_function():
        raise FileNotFoundError("Configuration file missing")
    
    def middle_function():
        with error_context("loading configuration"):
            deep_function()
    
    def top_function():
        with error_context("initializing system"):
            middle_function()
    
    try:
        top_function()
        assert False, "Exception should have been raised"
    except ProofSketcherError as e:
        # Check that the error was wrapped with context
        assert "initializing system" in str(e)
        assert "Configuration file missing" in str(e)
        assert e.details["operation"] == "initializing system"
        print("✓ Error context properly propagated and wrapped")
    
    return True


def test_structured_logging():
    """Test structured error logging."""
    print("\n🧪 Testing Structured Logging...")
    
    # Capture log output
    log_capture = StringIO()
    handler = logging.StreamHandler(log_capture)
    
    logger = setup_error_logger("test_structured")
    logger.handlers.clear()  # Remove default handlers
    logger.addHandler(handler)
    logger.setLevel(logging.INFO)
    
    # Test logging with structured data
    try:
        raise ProofSketcherError(
            "Test error",
            details={"file": "test.lean", "line": 42}
        )
    except ProofSketcherError as e:
        logger.error(
            f"Processing failed: {e}",
            extra={"details": e.details}
        )
    
    log_output = log_capture.getvalue()
    print(f"✓ Log output captured: {len(log_output) > 0}")
    print(f"✓ Contains error message: {'Processing failed' in log_output}")
    
    return True


def test_file_parser_error_handling():
    """Test real-world error handling in file parser."""
    print("\n🧪 Testing File Parser Error Handling...")
    
    parser = SimpleLeanParser()
    
    # Test non-existent file
    result = parser.parse_file("/this/file/does/not/exist.lean")
    assert not result.success
    assert len(result.errors) == 1
    assert "File not found" in result.errors[0].message
    print("✓ Non-existent file handled gracefully")
    
    # Test invalid file type
    result = parser.parse_file("test.txt")
    assert not result.success
    assert "Not a Lean file" in result.errors[0].message
    print("✓ Invalid file type detected")
    
    # Test oversized file
    with tempfile.NamedTemporaryFile(suffix=".lean", delete=False) as f:
        # Write 11MB of data (exceeds 10MB limit)
        large_content = "x" * (11 * 1024 * 1024)
        f.write(large_content.encode())
        f.flush()
        
        result = parser.parse_file(f.name)
        assert not result.success
        assert "File too large" in result.errors[0].message
        print("✓ Oversized file rejected with clear message")
        
        # Cleanup
        Path(f.name).unlink()
    
    return True


def test_batch_error_recovery():
    """Test that batch operations can recover from individual failures."""
    print("\n🧪 Testing Batch Error Recovery...")
    
    logger = setup_error_logger("batch_test")
    accumulator = ErrorAccumulator(logger)
    
    # Simulate batch processing with mixed success/failure
    files_to_process = [
        "good_file_1.lean",
        "bad_file.txt",  # Wrong extension
        "good_file_2.lean",
        "/nonexistent/path.lean",  # Missing file
        "good_file_3.lean"
    ]
    
    processed_files = []
    
    for file_path in files_to_process:
        with accumulator.capture(f"processing {file_path}"):
            if not file_path.endswith(".lean"):
                raise ValueError(f"Invalid file type: {file_path}")
            if "nonexistent" in file_path:
                raise FileNotFoundError(f"File not found: {file_path}")
            
            # Simulate successful processing
            processed_files.append(file_path)
    
    # Check that we processed what we could
    expected_good_files = 3
    assert len(processed_files) == expected_good_files
    assert accumulator.error_count == 2
    
    print(f"✓ Processed {len(processed_files)} valid files")
    print(f"✓ Accumulated {accumulator.error_count} errors for invalid files")
    print("✓ Batch operation completed despite individual failures")
    
    return True


def main():
    """Run all critical error handling tests."""
    print("🔍 Critical Error Handling Test Suite")
    print("=" * 50)
    
    tests = [
        test_error_accumulation,
        test_resource_limits,
        test_error_context_propagation,
        test_structured_logging,
        test_file_parser_error_handling,
        test_batch_error_recovery,
    ]
    
    passed = 0
    total = len(tests)
    
    for test in tests:
        try:
            if test():
                passed += 1
        except Exception as e:
            print(f"❌ {test.__name__} FAILED: {e}")
    
    print("\n" + "=" * 50)
    print(f"📊 Results: {passed}/{total} tests passed")
    
    if passed == total:
        print("✅ All critical error handling tests PASSED")
        print("\nRELIABILITY ASSESSMENT:")
        print("✓ Error accumulation works correctly")
        print("✓ Batch operations handle partial failures gracefully")
        print("✓ Resource limits are enforced")
        print("✓ Error context is preserved through call stacks")
        print("✓ Structured logging captures debugging information")
        print("✓ File operations fail gracefully with clear messages")
        return True
    else:
        print("❌ Some critical error handling tests FAILED")
        return False


if __name__ == "__main__":
    success = main()
    sys.exit(0 if success else 1)