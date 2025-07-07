"""
Manim Animation Generator

This module generates Manim scene code for mathematical theorem animations,
with intelligent formula handling and proof step visualization.
"""

import re
import logging
from typing import Dict, List, Optional, Tuple, Any
from pathlib import Path

from ..utils.security import validate_theorem_name


class TheoremAnimator:
    """Generate Manim animations for mathematical theorems."""
    
    def __init__(self):
        """Initialize the theorem animator."""
        self.logger = logging.getLogger(__name__)
        
        # Animation timing configuration
        self.default_timings = {
            "title_write": 1.5,
            "title_move": 1.0,
            "statement_write": 2.0,
            "statement_pause": 1.5,
            "step_transition": 1.0,
            "step_write": 2.0,
            "explanation_fade": 1.5,
            "qed_finale": 2.0
        }
        
        # Color scheme
        self.colors = {
            "title": "WHITE",
            "statement": "BLUE",
            "step": "YELLOW",
            "explanation": "GREEN", 
            "highlight": "RED",
            "qed": "GREEN"
        }
    
    def generate_animation_script(
        self, 
        theorem: Dict[str, Any], 
        sketch: Dict[str, Any],
        config: Optional[Dict[str, Any]] = None
    ) -> str:
        """Generate complete Manim scene code for theorem animation.
        
        Args:
            theorem: Theorem information dictionary
            sketch: Proof sketch with steps
            config: Optional animation configuration
            
        Returns:
            Complete Python script for Manim scene
        """
        try:
            # Validate theorem name
            theorem_name = theorem.get("name", "UnknownTheorem")
            validate_theorem_name(theorem_name)
        except Exception as e:
            self.logger.warning(f"Invalid theorem name: {e}")
            theorem_name = "Theorem"
        
        # Apply configuration
        timings = {**self.default_timings}
        if config and "timings" in config:
            timings.update(config["timings"])
        
        # Generate class name
        class_name = self._safe_class_name(theorem_name)
        
        # Build the script
        script = f'''"""
Generated Manim animation for theorem: {theorem_name}
"""
from manim import *
import numpy as np

class {class_name}(Scene):
    def construct(self):
        """Main animation sequence."""
        # Set up scene
        self.setup_scene()
        
        # Title sequence
        self.show_title()
        
        # Statement presentation
        self.show_statement()
        
        # Proof animation
        self.animate_proof()
        
        # Conclusion
        self.show_conclusion()
    
    def setup_scene(self):
        """Initialize scene elements."""
        self.title_text = "{self._escape_string(theorem_name)}"
        self.statement_text = r"{self._escape_latex(theorem.get('statement', ''))}"
        
        # Animation timing configuration
        self.timings = {timings}
        
        # Create title
        self.title = Text(
            self.title_text, 
            font_size=48, 
            color={self.colors["title"]}
        )
        
        # Create statement
        self.statement = MathTex(
            self.statement_text,
            font_size=36,
            color={self.colors["statement"]}
        )
        
    def show_title(self):
        """Animate title appearance and positioning."""
        # Write title
        self.play(
            Write(self.title),
            run_time=self.timings["title_write"]
        )
        self.wait(1)
        
        # Move title to corner
        self.play(
            self.title.animate.to_corner(UL).scale(0.6),
            run_time=self.timings["title_move"]
        )
        
    def show_statement(self):
        """Present the theorem statement."""
        # Position statement
        self.statement.move_to(UP * 2)
        
        # Animate statement
        self.play(
            Write(self.statement),
            run_time=self.timings["statement_write"]
        )
        self.wait(self.timings["statement_pause"])
        
    def animate_proof(self):
        """Animate the proof steps."""
{self._generate_proof_animation(sketch, timings)}
        
    def show_conclusion(self):
        """Show final QED."""
        # Clear previous content
        self.play(
            *[FadeOut(mob) for mob in self.mobjects if mob != self.title],
            run_time=1
        )
        
        # Create QED
        qed = Text(
            "∎", 
            font_size=96, 
            color={self.colors["qed"]}
        )
        
        # Animate QED with flourish
        self.play(
            GrowFromCenter(qed),
            run_time=self.timings["qed_finale"]
        )
        self.wait(2)
        
        # Final fade
        self.play(FadeOut(qed), FadeOut(self.title))
'''
        
        return script
    
    def _generate_proof_animation(self, sketch: Dict[str, Any], timings: Dict[str, float]) -> str:
        """Generate animation code for proof steps.
        
        Args:
            sketch: Proof sketch with steps
            timings: Timing configuration
            
        Returns:
            Indented Python code for proof animation
        """
        if not sketch or "key_steps" not in sketch:
            return "        # No proof steps available\n        self.wait(2)"
        
        steps = sketch["key_steps"]
        if not steps:
            return "        # No proof steps provided\n        self.wait(2)"
        
        code_lines = []
        code_lines.append("        # Move statement up to make room")
        code_lines.append("        self.play(")
        code_lines.append("            self.statement.animate.to_corner(UR).scale(0.7),")
        code_lines.append("            run_time=1")
        code_lines.append("        )")
        code_lines.append("")
        
        for i, step in enumerate(steps):
            step_number = i + 1
            description = step.get("description", f"Step {step_number}")
            mathematical_content = step.get("mathematical_content", "")
            tactics = step.get("tactics", [])
            
            # Create step content
            code_lines.append(f"        # Proof Step {step_number}")
            code_lines.append(f"        step_{i}_title = Text(")
            code_lines.append(f'            "Step {step_number}",')
            code_lines.append(f'            font_size=32,')
            code_lines.append(f'            color={self.colors["step"]}')
            code_lines.append(f"        ).to_edge(LEFT)")
            code_lines.append("")
            
            # Step description
            if description:
                code_lines.append(f"        step_{i}_desc = Text(")
                code_lines.append(f'            "{self._escape_string(description[:80])}",')
                code_lines.append(f'            font_size=24,')
                code_lines.append(f'            color={self.colors["explanation"]}')
                code_lines.append(f"        )")
                code_lines.append(f"        step_{i}_desc.next_to(step_{i}_title, DOWN, aligned_edge=LEFT)")
                code_lines.append("")
            
            # Mathematical content
            if mathematical_content:
                escaped_math = self._escape_latex(mathematical_content)
                code_lines.append(f"        step_{i}_math = MathTex(")
                code_lines.append(f'            r"{escaped_math}",')
                code_lines.append(f'            font_size=28')
                code_lines.append(f"        )")
                code_lines.append(f"        step_{i}_math.move_to(DOWN)")
                code_lines.append("")
            
            # Animation sequence for this step
            code_lines.append(f"        # Animate step {step_number}")
            
            if i > 0:  # Clear previous step
                code_lines.append("        self.play(")
                code_lines.append(f"            *[FadeOut(mob) for mob in self.mobjects")
                code_lines.append(f"              if mob not in [self.title, self.statement]],")
                code_lines.append(f"            run_time={timings['step_transition']}")
                code_lines.append("        )")
            
            code_lines.append("        self.play(")
            code_lines.append(f"            Write(step_{i}_title),")
            code_lines.append(f"            run_time={timings['step_write']}")
            code_lines.append("        )")
            
            if description:
                code_lines.append("        self.play(")
                code_lines.append(f"            FadeIn(step_{i}_desc),")
                code_lines.append(f"            run_time={timings['explanation_fade']}")
                code_lines.append("        )")
            
            if mathematical_content:
                code_lines.append("        self.play(")
                code_lines.append(f"            Write(step_{i}_math),")
                code_lines.append(f"            run_time={timings['step_write']}")
                code_lines.append("        )")
            
            # Show tactics if available
            if tactics:
                tactics_str = ", ".join(tactics[:3])  # Limit to 3 tactics
                code_lines.append(f"        tactics_{i} = Text(")
                code_lines.append(f'            "Tactics: {self._escape_string(tactics_str)}",')
                code_lines.append(f'            font_size=18,')
                code_lines.append(f'            color=GRAY')
                code_lines.append(f"        ).to_corner(DR)")
                code_lines.append("        self.play(")
                code_lines.append(f"            FadeIn(tactics_{i}),")
                code_lines.append("            run_time=1")
                code_lines.append("        )")
            
            code_lines.append("        self.wait(2)")
            code_lines.append("")
        
        return "\n".join(code_lines)
    
    def _safe_class_name(self, theorem_name: str) -> str:
        """Generate safe Python class name from theorem name.
        
        Args:
            theorem_name: Original theorem name
            
        Returns:
            Safe class name for Python
        """
        # Remove invalid characters and ensure valid identifier
        safe_name = re.sub(r'[^a-zA-Z0-9_]', '', theorem_name)
        
        # Ensure it starts with letter or underscore
        if not safe_name or safe_name[0].isdigit():
            safe_name = f"Theorem_{safe_name}"
        
        # Capitalize first letter
        safe_name = safe_name[0].upper() + safe_name[1:] if safe_name else "Theorem"
        
        # Ensure it's not too long
        if len(safe_name) > 50:
            safe_name = safe_name[:50]
        
        return safe_name or "TheoremAnimation"
    
    def _escape_latex(self, text: str) -> str:
        """Escape and convert text for LaTeX/MathTex.
        
        Args:
            text: Input text with mathematical notation
            
        Returns:
            LaTeX-safe text
        """
        if not text:
            return ""
        
        # Handle Lean 4 notation
        conversions = {
            "∀": r"\\forall ",
            "∃": r"\\exists ",
            "→": r"\\to ",
            "↔": r"\\leftrightarrow ",
            "¬": r"\\neg ",
            "∧": r"\\land ",
            "∨": r"\\lor ",
            "ℕ": r"\\mathbb{N}",
            "ℤ": r"\\mathbb{Z}",
            "ℚ": r"\\mathbb{Q}",
            "ℝ": r"\\mathbb{R}",
            "ℂ": r"\\mathbb{C}",
            "≤": r"\\leq ",
            "≥": r"\\geq ",
            "≠": r"\\neq ",
            "∈": r"\\in ",
            "∉": r"\\notin ",
            "⊆": r"\\subseteq ",
            "⊂": r"\\subset ",
            "∪": r"\\cup ",
            "∩": r"\\cap ",
            "∅": r"\\emptyset",
            # Function notation
            ":": r":",
            "⟨": r"\\langle ",
            "⟩": r"\\rangle ",
            # Common operators
            "·": r"\\cdot ",
            "×": r"\\times ",
            "÷": r"\\div ",
        }
        
        result = text
        for symbol, latex in conversions.items():
            result = result.replace(symbol, latex)
        
        # Escape special LaTeX characters
        latex_escapes = {
            "\\": r"\\\\",
            "{": r"\\{",
            "}": r"\\}",
            "$": r"\\$",
            "&": r"\\&",
            "%": r"\\%",
            "#": r"\\#",
            "^": r"\\hat{}", 
            "_": r"\\_",
            "~": r"\\sim ",
        }
        
        for char, escape in latex_escapes.items():
            if char != "\\" or not any(cmd in result for cmd in [r"\\forall", r"\\exists", r"\\to"]):
                result = result.replace(char, escape)
        
        # Handle subscripts and superscripts more carefully
        result = re.sub(r'([a-zA-Z])_([a-zA-Z0-9]+)', r'\1_{\2}', result)
        result = re.sub(r'([a-zA-Z])\^([a-zA-Z0-9]+)', r'\1^{\2}', result)
        
        return result
    
    def _escape_string(self, text: str) -> str:
        """Escape string for Python string literal.
        
        Args:
            text: Input text
            
        Returns:
            Escaped string safe for Python literals
        """
        if not text:
            return ""
        
        # Escape quotes and backslashes
        result = text.replace('\\', '\\\\')
        result = result.replace('"', '\\"')
        result = result.replace("'", "\\'")
        
        # Handle newlines
        result = result.replace('\n', '\\n')
        result = result.replace('\r', '\\r')
        result = result.replace('\t', '\\t')
        
        return result
    
    def generate_simple_animation(
        self, 
        theorem_name: str, 
        statement: str,
        steps: Optional[List[str]] = None
    ) -> str:
        """Generate a simple animation for basic theorems.
        
        Args:
            theorem_name: Name of the theorem
            statement: Mathematical statement
            steps: Optional list of proof steps
            
        Returns:
            Simple Manim script
        """
        class_name = self._safe_class_name(theorem_name)
        escaped_statement = self._escape_latex(statement)
        
        steps_code = ""
        if steps:
            for i, step in enumerate(steps[:3]):  # Limit to 3 steps
                steps_code += f'''
        # Step {i+1}
        step_{i} = Text("{self._escape_string(step)}", font_size=24)
        step_{i}.shift(DOWN * {i+1})
        self.play(Write(step_{i}))
        self.wait(1.5)
'''
        
        return f'''from manim import *

class {class_name}(Scene):
    def construct(self):
        # Title
        title = Text("{self._escape_string(theorem_name)}", font_size=42)
        self.play(Write(title))
        self.wait(1)
        self.play(title.animate.to_corner(UL).scale(0.7))
        
        # Statement  
        statement = MathTex(r"{escaped_statement}", font_size=32)
        self.play(Write(statement))
        self.wait(2)
        {steps_code}
        
        # QED
        qed = Text("∎", font_size=64, color=GREEN)
        self.play(GrowFromCenter(qed))
        self.wait(2)
'''
    
    def validate_script(self, script: str) -> Tuple[bool, Optional[str]]:
        """Validate generated Manim script.
        
        Args:
            script: Generated Python script
            
        Returns:
            Tuple of (is_valid, error_message)
        """
        try:
            # Check syntax
            compile(script, '<string>', 'exec')
            
            # Check for required Manim elements
            required_elements = [
                "from manim import",
                "class",
                "Scene",
                "def construct"
            ]
            
            for element in required_elements:
                if element not in script:
                    return False, f"Missing required element: {element}"
            
            return True, None
            
        except SyntaxError as e:
            return False, f"Syntax error: {e}"
        except Exception as e:
            return False, f"Validation error: {e}"