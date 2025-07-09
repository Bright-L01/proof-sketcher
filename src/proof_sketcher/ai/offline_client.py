"""
Offline fallback generator for when AI services are unavailable.
Provides template-based responses for basic functionality.
"""

import re
import logging
from typing import Dict, Any

from .base_client import AIClient


class OfflineClient(AIClient):
    """Offline fallback generator using templates.
    
    This provides basic functionality when AI services are unavailable,
    ensuring the application can still function in a degraded mode.
    """
    
    def __init__(self):
        """Initialize the offline client."""
        self.logger = logging.getLogger(__name__)
        self.logger.info("Using offline fallback generator")
    
    def generate(self, prompt: str, **kwargs) -> str:
        """Generate template response based on prompt analysis.
        
        Args:
            prompt: Input prompt
            **kwargs: Additional parameters (ignored)
            
        Returns:
            Template-based response
        """
        prompt_lower = prompt.lower()
        
        # Analyze prompt type
        if self._is_proof_sketch_request(prompt_lower):
            return self._generate_proof_sketch(prompt)
        elif self._is_eli5_request(prompt_lower):
            return self._generate_eli5_explanation(prompt)
        elif self._is_tactic_request(prompt_lower):
            return self._generate_tactic_explanation(prompt)
        elif self._is_step_by_step_request(prompt_lower):
            return self._generate_step_by_step(prompt)
        else:
            return self._generate_generic_explanation(prompt)
    
    def is_available(self) -> bool:
        """Offline client is always available.
        
        Returns:
            Always True
        """
        return True
    
    def get_info(self) -> Dict[str, Any]:
        """Get information about the offline client.
        
        Returns:
            Dictionary with client information
        """
        info = super().get_info()
        info.update({
            "provider": "Offline Templates",
            "mode": "fallback",
            "features": ["proof_sketch", "eli5", "tactics", "step_by_step"]
        })
        return info
    
    def _is_proof_sketch_request(self, prompt: str) -> bool:
        """Check if prompt is requesting a proof sketch."""
        keywords = ["proof sketch", "explain.*theorem", "natural language.*proof"]
        return any(re.search(keyword, prompt) for keyword in keywords)
    
    def _is_eli5_request(self, prompt: str) -> bool:
        """Check if prompt is requesting an ELI5 explanation."""
        keywords = ["eli5", "explain.*five", "simple.*explanation", "beginner"]
        return any(re.search(keyword, prompt) for keyword in keywords)
    
    def _is_tactic_request(self, prompt: str) -> bool:
        """Check if prompt is requesting tactic explanation."""
        keywords = ["tactic", "lean.*command", "proof.*method"]
        return any(re.search(keyword, prompt) for keyword in keywords)
    
    def _is_step_by_step_request(self, prompt: str) -> bool:
        """Check if prompt is requesting step-by-step explanation."""
        keywords = ["step.?by.?step", "detailed.*walk", "each.*step"]
        return any(re.search(keyword, prompt) for keyword in keywords)
    
    def _extract_theorem_info(self, prompt: str) -> Dict[str, str]:
        """Extract theorem information from prompt."""
        info = {
            "name": "the theorem",
            "statement": "the given statement",
            "type": "mathematical property"
        }
        
        # Try to extract theorem name
        name_match = re.search(r"theorem\s+(\w+)", prompt, re.IGNORECASE)
        if name_match:
            info["name"] = name_match.group(1)
        
        # Try to identify theorem type
        if "commutative" in prompt.lower() or "comm" in prompt.lower():
            info["type"] = "commutativity property"
        elif "associative" in prompt.lower() or "assoc" in prompt.lower():
            info["type"] = "associativity property"
        elif "distributive" in prompt.lower():
            info["type"] = "distributivity property"
        elif "identity" in prompt.lower() or "neutral" in prompt.lower():
            info["type"] = "identity property"
        
        return info
    
    def _generate_proof_sketch(self, prompt: str) -> str:
        """Generate a template proof sketch."""
        info = self._extract_theorem_info(prompt)
        
        return f"""{{
  "theorem_name": "{info['name']}",
  "introduction": "This theorem establishes {info['type']}. The proof demonstrates how the property holds under the given conditions.",
  "key_steps": [
    {{
      "step_number": 1,
      "description": "Establish the base case or initial conditions",
      "mathematical_content": "We begin by examining the fundamental structure",
      "tactics": ["intro", "unfold"]
    }},
    {{
      "step_number": 2,
      "description": "Apply the main mathematical principle",
      "mathematical_content": "Using the core property, we transform the expression",
      "tactics": ["rewrite", "simplify"]
    }},
    {{
      "step_number": 3,
      "description": "Complete the proof",
      "mathematical_content": "The desired result follows directly",
      "tactics": ["exact", "rfl"]
    }}
  ],
  "conclusion": "This completes the proof of {info['type']}. The result shows that the property holds as required.",
  "difficulty_level": "intermediate",
  "mathematical_areas": ["algebra", "logic"],
  "prerequisites": ["basic algebra", "proof techniques"]
}}"""
    
    def _generate_eli5_explanation(self, prompt: str) -> str:
        """Generate a simple ELI5 explanation."""
        info = self._extract_theorem_info(prompt)
        
        return f"""Let me explain {info['name']} in simple terms!

Imagine you have building blocks. This theorem is like a rule about how these blocks work together.

Think of it this way:
- When you arrange blocks in a certain way, you get a pattern
- This theorem says that pattern will always work the same way
- No matter how many blocks you use!

It's like knowing that 2 + 3 always equals 5, no matter when or where you do the math.

In grown-up math terms, this is called {info['type']}, and mathematicians use it all the time to solve bigger problems!

Note: This is a simplified template explanation. For more detailed insights, please configure an AI service."""
    
    def _generate_tactic_explanation(self, prompt: str) -> str:
        """Generate a tactic explanation."""
        return """This proof uses several key Lean tactics:

**intro**: Introduces hypotheses into the context
- Used to bring variables and assumptions into scope
- Essential for starting most proofs

**rewrite**: Transforms expressions using equalities
- Applied when we have an equation that can simplify our goal
- Can be used with ← for reverse rewriting

**simp**: Simplifies expressions automatically
- Uses a database of simplification rules
- Great for routine algebraic manipulations

**exact**: Provides the exact term that solves the goal
- Used when we have constructed the precise answer
- Completes the proof

**rfl**: Reflexivity - proves things equal to themselves
- Used for definitional equalities
- Often the final step in equality proofs

Note: This is a generic template. For theorem-specific tactic analysis, please configure an AI service."""
    
    def _generate_step_by_step(self, prompt: str) -> str:
        """Generate a step-by-step walkthrough."""
        info = self._extract_theorem_info(prompt)
        
        return f"""Step-by-Step Proof Walkthrough for {info['name']}:

**Step 1: Understanding the Goal**
- We need to prove {info['type']}
- Let's identify what we're given and what we need to show

**Step 2: Setting Up**
- Introduce any necessary variables
- State our assumptions clearly
- Write down what we want to prove

**Step 3: Main Argument**
- Apply the relevant mathematical principle
- Show how the left side transforms to the right side
- Use algebraic properties as needed

**Step 4: Simplification**
- Simplify both sides of our equation
- Apply known identities
- Reduce to a simpler form

**Step 5: Conclusion**
- Verify our result matches the goal
- Confirm all steps are valid
- Complete the proof

Each step builds on the previous one, creating a logical chain from our assumptions to our conclusion.

Note: This is a template walkthrough. For specific proof details, please configure an AI service."""
    
    def _generate_generic_explanation(self, prompt: str) -> str:
        """Generate a generic explanation."""
        return """This mathematical concept represents an important principle in formal reasoning.

Key aspects:
1. It establishes a fundamental property
2. The proof uses standard mathematical techniques
3. The result has applications in various mathematical contexts

The formal proof proceeds by:
- Setting up the necessary framework
- Applying relevant theorems and lemmas
- Concluding with the desired result

This type of result is commonly used in mathematical proofs and provides a building block for more complex theorems.

Note: This is a generic template response. For detailed explanations tailored to specific theorems, please configure an AI service with your API credentials."""