"""Property-based tests using Hypothesis.

This module uses property-based testing to find edge cases and ensure
robust behavior across a wide range of inputs.
"""

import json
import string
import tempfile
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, List

import pytest
from hypothesis import assume, given, settings, strategies as st
from hypothesis.stateful import Bundle, RuleBasedStateMachine, rule
from pydantic import ValidationError

from proof_sketcher.core.exceptions import (
    InputValidationError,
    ProofSketcherError,
    ValidationError as PSValidationError,
)
from proof_sketcher.core.utils import (
    calculate_hash,
    chunk_list,
    deep_merge,
    flatten_dict,
    format_duration,
    generate_cache_key,
    sanitize_filename,
    truncate_text,
)
from proof_sketcher.generator.models import ProofSketch, ProofStep
from proof_sketcher.parser.models import ParseError, ParseResult, TheoremInfo


# Custom strategies for domain-specific types
@st.composite
def theorem_names(draw):
    """Generate valid theorem names."""
    prefix = draw(st.sampled_from(["theorem", "lemma", "proposition", "corollary"]))
    suffix = draw(st.text(alphabet=string.ascii_lowercase + "_", min_size=1, max_size=20))
    return f"{prefix}_{suffix}"


@st.composite
def lean_expressions(draw):
    """Generate Lean-like mathematical expressions."""
    templates = [
        "∀ {var} : {type}, {prop}",
        "∃ {var} : {type}, {prop}",
        "{term} = {term}",
        "{term} → {term}",
        "{term} ∧ {term}",
        "{term} ∨ {term}",
    ]
    
    var = draw(st.sampled_from(["x", "y", "n", "m", "a", "b"]))
    type_name = draw(st.sampled_from(["Nat", "Int", "Real", "Prop"]))
    term = draw(st.sampled_from([var, "0", "1", f"{var} + 1", f"{var} * 2"]))
    prop = draw(st.sampled_from([f"{var} > 0", f"{var} = {var}", "True", "False"]))
    
    template = draw(st.sampled_from(templates))
    return template.format(var=var, type=type_name, term=term, prop=prop)


@st.composite
def proof_tactics(draw):
    """Generate valid proof tactics."""
    tactics = ["rfl", "simp", "exact", "apply", "intro", "cases", "induction"]
    return draw(st.lists(st.sampled_from(tactics), min_size=1, max_size=5))


class TestCoreUtilsProperties:
    """Property-based tests for core utilities."""
    
    @given(st.lists(st.text()))
    def test_generate_cache_key_deterministic(self, args):
        """Test that cache key generation is always deterministic."""
        key1 = generate_cache_key(*args)
        key2 = generate_cache_key(*args)
        assert key1 == key2
        assert len(key1) == 64  # SHA256 hex length
    
    @given(st.dictionaries(st.text(), st.text()))
    def test_generate_cache_key_kwargs_order_independent(self, kwargs):
        """Test that kwarg order doesn't affect cache key."""
        # Create two different orderings
        items = list(kwargs.items())
        if len(items) > 1:
            # Swap first two items
            items[0], items[1] = items[1], items[0]
            kwargs_reordered = dict(items)
            
            key1 = generate_cache_key(**kwargs)
            key2 = generate_cache_key(**kwargs_reordered)
            assert key1 == key2
    
    @given(st.text())
    @settings(max_examples=100)
    def test_sanitize_filename_always_valid(self, filename):
        """Test that sanitized filenames are always valid."""
        sanitized = sanitize_filename(filename)
        
        # Check properties
        assert isinstance(sanitized, str)
        assert len(sanitized) > 0
        assert len(sanitized) <= 255
        
        # No invalid characters
        invalid_chars = '<>:"/\\|?*'
        assert all(c not in sanitized for c in invalid_chars)
        
        # No leading/trailing spaces or dots
        assert not sanitized.startswith(' ')
        assert not sanitized.endswith(' ')
        assert not sanitized.startswith('.')
        assert not sanitized.endswith('.')
    
    @given(st.text(), st.integers(min_value=1, max_value=1000))
    def test_truncate_text_length_constraint(self, text, max_length):
        """Test that truncated text respects length constraint."""
        truncated = truncate_text(text, max_length)
        assert len(truncated) <= max_length
        
        if len(text) <= max_length:
            assert truncated == text
        else:
            assert truncated.endswith("...")
    
    @given(st.floats(min_value=0, max_value=1e6))
    def test_format_duration_always_readable(self, seconds):
        """Test that duration formatting always produces readable output."""
        assume(not (seconds != seconds))  # Skip NaN
        
        formatted = format_duration(seconds)
        assert isinstance(formatted, str)
        assert len(formatted) > 0
        
        # Check format based on duration
        if seconds < 1:
            assert formatted.endswith("ms")
        elif seconds < 60:
            assert formatted.endswith("s")
        elif seconds < 3600:
            assert "m" in formatted
        else:
            assert "h" in formatted
    
    @given(st.dictionaries(st.text(), st.integers()))
    def test_flatten_dict_preserves_values(self, d):
        """Test that flattening preserves all values."""
        flattened = flatten_dict(d)
        
        # All values should be preserved
        original_values = set(d.values())
        flattened_values = set(flattened.values())
        assert original_values == flattened_values
    
    @given(
        st.dictionaries(st.text(), st.integers()),
        st.dictionaries(st.text(), st.integers())
    )
    def test_deep_merge_preserves_non_overlapping(self, base, update):
        """Test that deep merge preserves non-overlapping keys."""
        result = deep_merge(base, update)
        
        # Non-overlapping keys from base should be preserved
        for key in base:
            if key not in update:
                assert result[key] == base[key]
        
        # All keys from update should be in result
        for key in update:
            assert result[key] == update[key]
    
    @given(st.lists(st.integers()), st.integers(min_value=1, max_value=100))
    def test_chunk_list_completeness(self, lst, chunk_size):
        """Test that chunking preserves all elements."""
        chunks = chunk_list(lst, chunk_size)
        
        # Flatten chunks
        flattened = []
        for chunk in chunks:
            flattened.extend(chunk)
        
        # Should have all original elements
        assert flattened == lst
        
        # Each chunk should be at most chunk_size
        for chunk in chunks[:-1]:  # All but last
            assert len(chunk) == chunk_size
        if chunks:
            assert len(chunks[-1]) <= chunk_size
    
    @given(st.binary())
    def test_calculate_hash_deterministic(self, data):
        """Test that hash calculation is deterministic."""
        hash1 = calculate_hash(data)
        hash2 = calculate_hash(data)
        
        assert hash1 == hash2
        assert len(hash1) == 64  # SHA256
        assert all(c in "0123456789abcdef" for c in hash1)


class TestModelsProperties:
    """Property-based tests for data models."""
    
    @given(
        name=theorem_names(),
        statement=lean_expressions(),
        proof=st.text(min_size=1),
        line_number=st.integers(min_value=1, max_value=10000)
    )
    def test_theorem_info_validation(self, name, statement, proof, line_number):
        """Test TheoremInfo validation with various inputs."""
        theorem = TheoremInfo(
            name=name,
            statement=statement,
            proof=proof,
            line_number=line_number
        )
        
        assert theorem.name == name
        assert theorem.statement == statement
        assert theorem.proof == proof
        assert theorem.line_number == line_number
    
    @given(
        message=st.text(min_size=1),
        line_number=st.integers(min_value=0, max_value=10000),
        column=st.integers(min_value=0, max_value=200)
    )
    def test_parse_error_creation(self, message, line_number, column):
        """Test ParseError creation with various inputs."""
        error = ParseError(
            message=message,
            line_number=line_number,
            column=column
        )
        
        assert error.message == message
        assert error.line_number == line_number
        assert error.column == column
        assert error.error_type == "parse_error"
        assert error.severity == "error"
    
    @given(st.lists(
        st.builds(
            TheoremInfo,
            name=theorem_names(),
            statement=lean_expressions()
        ),
        max_size=10
    ))
    def test_parse_result_consistency(self, theorems):
        """Test ParseResult consistency properties."""
        result = ParseResult(theorems=theorems)
        
        assert result.has_theorems == (len(theorems) > 0)
        assert not result.has_errors
        assert result.success
        
        # Test get_theorem_by_name
        for theorem in theorems:
            found = result.get_theorem_by_name(theorem.name)
            assert found == theorem
    
    @given(
        theorem_name=theorem_names(),
        theorem_statement=lean_expressions(),
        introduction=st.text(min_size=1, max_size=200),
        conclusion=st.text(min_size=1, max_size=200),
        difficulty=st.sampled_from(["trivial", "easy", "intermediate", "hard", "expert"])
    )
    def test_proof_sketch_validation(self, theorem_name, theorem_statement, 
                                   introduction, conclusion, difficulty):
        """Test ProofSketch validation with various inputs."""
        sketch = ProofSketch(
            theorem_name=theorem_name,
            theorem_statement=theorem_statement,
            introduction=introduction,
            key_steps=[],  # Empty steps for simplicity
            conclusion=conclusion,
            difficulty_level=difficulty
        )
        
        assert sketch.theorem_name == theorem_name
        assert sketch.theorem_statement == theorem_statement
        assert sketch.introduction == introduction
        assert sketch.conclusion == conclusion
        assert sketch.difficulty_level == difficulty


class TestExceptionProperties:
    """Property-based tests for exception handling."""
    
    @given(
        message=st.text(min_size=1),
        details=st.dictionaries(st.text(), st.text()),
        error_code=st.text(alphabet=string.ascii_uppercase + "_", min_size=3, max_size=20)
    )
    def test_proof_sketcher_error_properties(self, message, details, error_code):
        """Test ProofSketcherError properties."""
        error = ProofSketcherError(message, details=details, error_code=error_code)
        
        assert error.message == message
        assert error.details == details
        assert error.error_code == error_code
        
        # String representation
        str_repr = str(error)
        assert message in str_repr
        if error_code:
            assert error_code in str_repr


class CacheStateMachine(RuleBasedStateMachine):
    """Stateful testing for cache-like behavior."""
    
    def __init__(self):
        super().__init__()
        self.cache = {}
        self.access_count = {}
    
    keys = Bundle('keys')
    values = Bundle('values')
    
    @rule(
        key=st.text(min_size=1, max_size=20),
        value=st.integers(),
        target=keys
    )
    def put(self, key, value):
        """Put a value in the cache."""
        self.cache[key] = value
        self.access_count[key] = self.access_count.get(key, 0) + 1
        return key
    
    @rule(key=keys)
    def get(self, key):
        """Get a value from the cache."""
        value = self.cache.get(key)
        if value is not None:
            self.access_count[key] = self.access_count.get(key, 0) + 1
        
        # Property: getting an existing key returns its value
        if key in self.cache:
            assert value == self.cache[key]
    
    @rule(key=keys)
    def delete(self, key):
        """Delete a value from the cache."""
        existed = key in self.cache
        if existed:
            del self.cache[key]
            # Don't remove from access_count to track history
        
        # Property: deleted keys are no longer in cache
        assert key not in self.cache
    
    @rule()
    def clear(self):
        """Clear the cache."""
        self.cache.clear()
        
        # Property: cache is empty after clear
        assert len(self.cache) == 0
    
    @rule()
    def check_consistency(self):
        """Check cache consistency."""
        # Property: all keys in cache have been accessed at least once
        for key in self.cache:
            assert key in self.access_count
            assert self.access_count[key] >= 1


class TestStatefulProperties:
    """Test stateful properties using Hypothesis."""
    
    def test_cache_state_machine(self):
        """Test cache behavior with state machine."""
        # This will generate random sequences of operations
        # and check that all invariants hold
        CacheStateMachine.TestCase.settings = settings(max_examples=50)
        state_machine_test = CacheStateMachine.TestCase()
        state_machine_test.runTest()


class TestPathologicalInputs:
    """Test with pathological inputs to find edge cases."""
    
    @given(st.text(
        alphabet=st.characters(blacklist_categories=["Cc", "Cs"]),
        min_size=0,
        max_size=10000
    ))
    def test_sanitize_filename_unicode_handling(self, text):
        """Test filename sanitization with Unicode inputs."""
        try:
            sanitized = sanitize_filename(text)
            # Should always produce valid ASCII filename
            assert sanitized.isascii()
            assert len(sanitized) > 0
        except Exception as e:
            # Should not raise exceptions
            pytest.fail(f"sanitize_filename raised {type(e).__name__}: {e}")
    
    @given(st.dictionaries(
        st.text(max_size=10),
        st.recursive(
            st.integers() | st.text(max_size=10) | st.booleans(),
            lambda children: st.dictionaries(st.text(max_size=10), children, max_size=3),
            max_leaves=10
        ),
        max_size=5
    ))
    def test_deep_merge_nested_structures(self, base):
        """Test deep merge with deeply nested structures."""
        # Create a modified copy
        import copy
        update = copy.deepcopy(base)
        
        # Modify some values
        for key in list(update.keys())[:len(update)//2]:
            if isinstance(update[key], dict) and update[key]:
                # Modify nested dict
                nested_key = list(update[key].keys())[0]
                update[key][nested_key] = "modified"
            else:
                update[key] = "modified"
        
        # Merge
        result = deep_merge(base, update)
        
        # Check that all keys from update are in result
        def check_nested(d1, d2):
            for k, v in d1.items():
                assert k in d2
                if isinstance(v, dict) and isinstance(d2[k], dict):
                    check_nested(v, d2[k])
                else:
                    assert d2[k] == v
        
        check_nested(update, result)
    
    @given(st.lists(st.text(), min_size=0, max_size=1000))
    def test_cache_key_generation_performance(self, items):
        """Test cache key generation doesn't degrade with many items."""
        import time
        
        start = time.time()
        key = generate_cache_key(*items)
        duration = time.time() - start
        
        # Should complete in reasonable time even with many items
        assert duration < 1.0  # 1 second max
        assert len(key) == 64


class TestPropertyInvariants:
    """Test invariants that should always hold."""
    
    @given(st.data())
    def test_parse_result_invariants(self, data):
        """Test ParseResult invariants."""
        # Generate theorems and errors
        theorems = data.draw(st.lists(
            st.builds(TheoremInfo, name=theorem_names(), statement=lean_expressions()),
            max_size=5
        ))
        errors = data.draw(st.lists(
            st.builds(ParseError, message=st.text(min_size=1)),
            max_size=5
        ))
        
        success = data.draw(st.booleans())
        
        result = ParseResult(
            theorems=theorems,
            errors=errors,
            success=success
        )
        
        # Invariants
        assert result.has_theorems == (len(theorems) > 0)
        assert result.has_errors == (len(errors) > 0)
        
        # If there are errors, it's common (but not required) to not be successful
        # This is a soft invariant - we just check the relationship makes sense
        if errors and not success:
            assert result.has_errors
    
    @given(st.lists(st.integers(), min_size=1))
    def test_chunk_list_invariants(self, lst):
        """Test chunk_list invariants."""
        for chunk_size in range(1, min(len(lst) + 1, 10)):
            chunks = chunk_list(lst, chunk_size)
            
            # Invariant 1: Concatenating chunks gives original list
            concatenated = []
            for chunk in chunks:
                concatenated.extend(chunk)
            assert concatenated == lst
            
            # Invariant 2: All chunks except possibly the last have chunk_size elements
            for chunk in chunks[:-1]:
                assert len(chunk) == chunk_size
            
            # Invariant 3: Last chunk has at most chunk_size elements
            if chunks:
                assert len(chunks[-1]) <= chunk_size
            
            # Invariant 4: Number of chunks is correct
            expected_chunks = (len(lst) + chunk_size - 1) // chunk_size
            assert len(chunks) == expected_chunks


if __name__ == "__main__":
    pytest.main([__file__, "-v", "--hypothesis-show-statistics"])