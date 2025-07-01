"""Prompt templates for natural language generation using Jinja2."""

from typing import List, Optional

from jinja2 import BaseLoader, Environment, Template

from ..parser.models import TheoremInfo
from .models import GenerationConfig, GenerationType


class PromptTemplates:
    """Collection of Jinja2 templates for different generation types."""

    def __init__(self):
        """Initialize with Jinja2 environment."""
        self.env = Environment(
            loader=BaseLoader(), trim_blocks=True, lstrip_blocks=True
        )

        # Add custom filters
        self.env.filters["format_dependencies"] = self._format_dependencies
        self.env.filters["format_statement"] = self._format_statement

    def _format_dependencies(self, dependencies: List[str]) -> str:
        """Format dependencies list for display."""
        if not dependencies:
            return "None"
        if len(dependencies) <= 3:
            return ", ".join(dependencies)
        return f"{', '.join(dependencies[:3])}, and {len(dependencies) - 3} others"

    def _format_statement(self, statement: str) -> str:
        """Format theorem statement for better readability."""
        # Clean up common Lean syntax for natural language
        statement = statement.replace("∀", "for all")
        statement = statement.replace("∃", "there exists")
        statement = statement.replace("→", "implies")
        statement = statement.replace("↔", "if and only if")
        statement = statement.replace("¬", "not")
        statement = statement.replace("∧", "and")
        statement = statement.replace("∨", "or")
        return statement

    @property
    def proof_sketch_template(self) -> Template:
        """Enhanced template for generating structured proof sketches with better prompt engineering."""
        template_str = """
You are a distinguished mathematics professor with expertise in {{ mathematical_context or "formal mathematics" }}. Your mission is to create an exceptional proof sketch that bridges formal mathematics and human intuition.

## 🎯 OBJECTIVE
Transform the formal proof below into a clear, pedagogical explanation that reveals the underlying mathematical beauty and logic.

## 📚 THEOREM ANALYSIS
**Name:** {{ theorem_name }}
**Statement:** {{ theorem_statement | format_statement }}
{% if dependencies %}**Dependencies:** {{ dependencies | format_dependencies }}{% endif %}
{% if docstring %}**Context:** {{ docstring }}{% endif %}
{% if mathematical_context %}**Mathematical Domain:** {{ mathematical_context }}{% endif %}
{% if proof_text %}
**Formal Proof:**
```lean
{{ proof_text }}
```
{% endif %}

## 💡 EXAMPLE OF EXCELLENT EXPLANATION
Here's how a master teacher would approach a similar theorem:

**For theorem "Identity element uniqueness in groups":**
1. **Big Picture**: "We're proving something fundamental - every group has exactly one identity element. This is like showing there's only one 'neutral' element in any algebraic system."
2. **Strategy**: "We'll use proof by contradiction - assume two identities exist, then show they must be the same."
3. **Key Insight**: "The group axioms themselves force uniqueness - it's not an accident but a logical necessity."

## 🎓 YOUR TASK
Create a {{ config.verbosity }} proof sketch following this structure:

### PART 1: MATHEMATICAL INTUITION
- What does this theorem really say in plain language?
- Why should someone care about this result?
- What would happen if this theorem weren't true?
- How does it connect to broader mathematical themes?

### PART 2: PROOF STRATEGY
- What's the high-level approach?
- What are the 3-5 key logical moves?
- What's the most elegant or clever part?
- What potential pitfalls must be avoided?

### PART 3: STEP-BY-STEP BREAKDOWN
For each major step:
- **Goal**: What are we trying to achieve?
- **Method**: How do we achieve it?
- **Justification**: Why does this work?
- **Insight**: What's the key mathematical idea?

### PART 4: REFLECTION
- What's the main takeaway?
- How does this fit into the larger mathematical picture?
- What techniques or patterns could be applied elsewhere?

## 🔧 TECHNICAL SPECIFICATIONS
- **Audience Level**: {{ config.verbosity }} (adapt complexity accordingly)
- **Tone**: Enthusiastic but precise, like the best mathematics teachers
- **Length**: Comprehensive but not overwhelming
- **Focus**: Mathematical reasoning and intuition, not just formal steps
{% if config.include_reasoning %}
- **Include**: Detailed reasoning behind each choice and technique
{% endif %}

## 📊 OUTPUT FORMAT
Respond with this exact JSON structure:

```json
{
  "theorem_name": "{{ theorem_name }}",
  "mathematical_significance": "Why this theorem matters in mathematics",
  "intuitive_explanation": "What this means in everyday mathematical language",
  "proof_strategy": {
    "approach": "High-level strategy (proof by contradiction, construction, induction, etc.)",
    "key_insight": "The crucial mathematical idea that makes the proof work",
    "potential_difficulties": "Common stumbling blocks or subtle points"
  },
  "key_steps": [
    {
      "step_number": 1,
      "goal": "What we're trying to accomplish in this step",
      "method": "The mathematical technique or approach used",
      "mathematical_content": "The formal mathematical details",
      "lean_tactics": ["specific", "lean", "tactics", "used"],
      "intuition": "Why this step works and why it's necessary",
      "connects_to": "How this step builds on previous steps or enables future ones"
    }
  ],
  "mathematical_reflection": {
    "main_insight": "The key mathematical principle demonstrated",
    "broader_context": "How this fits into the mathematical landscape",
    "applications": ["where", "this", "technique", "appears", "elsewhere"],
    "generalizations": "How this result could be extended or generalized"
  },
  "pedagogical_notes": {
    "difficulty_level": "beginner|intermediate|advanced",
    "mathematical_areas": ["primary", "mathematical", "fields"],
    "prerequisites": ["essential", "background", "knowledge"],
    "common_misconceptions": ["typical", "student", "mistakes", "to", "avoid"]
  }
}
```

## 🌟 REMEMBER
Your goal is not just to explain the proof, but to reveal the mathematical thinking that makes it beautiful and inevitable. Help the reader see mathematics the way you do - as a landscape of interconnected ideas and elegant reasoning.
"""
        return self.env.from_string(template_str)

    @property
    def eli5_template(self) -> Template:
        """Enhanced template for ELI5 explanations using analogies and storytelling."""
        template_str = """
You are a gifted science communicator like Bill Nye or Neil deGrasse Tyson, but for mathematics. Your superpower is making complex math feel like an exciting discovery that anyone can understand and appreciate.

## 🎪 THE MATHEMATICAL DISCOVERY
**What We're Exploring:** {{ theorem_name }}
**The Big Idea:** {{ theorem_statement | format_statement }}
{% if dependencies %}**This Builds On:** {{ dependencies | format_dependencies }}{% endif %}
{% if docstring %}**Why It Matters:** {{ docstring }}{% endif %}
{% if mathematical_context %}**Mathematical World:** {{ mathematical_context }}{% endif %}

## 🌟 MASTER CLASS EXAMPLE
Here's how a great communicator would explain a mathematical concept:

**Topic: "Why every group has exactly one identity element"**
> "Imagine you're organizing the world's most exclusive club - let's call it the Math Club. This club has a special rule: there's exactly one member who doesn't change anything when they show up. If Alice comes to a meeting, everything stays the same. If Bob comes with Alice, it's still the same as just Bob being there. Alice is like the 'neutral' member.
> 
> Now here's the kicker - our theorem proves that there can only be ONE Alice in any Math Club that follows certain rules. It's impossible to have two neutral members! It's like trying to have two different 'zeros' in arithmetic - the math itself won't let it happen."

## 🎯 YOUR MISSION
Create an {{ config.verbosity }} explanation that makes someone think "Wow, I never knew math could be this cool!"

### STORYTELLING FRAMEWORK
1. **Hook**: Start with something surprising or relatable
2. **Analogy**: Use a perfect real-world comparison
3. **Discovery**: Walk through the "aha!" moment
4. **Significance**: Why this changes everything
5. **Wonder**: Leave them curious about more math

### COMMUNICATION PRINCIPLES
- **No Jargon**: Replace technical terms with everyday language
- **Visual Thinking**: Help them picture what's happening
- **Emotional Connection**: Make them feel the beauty and surprise
- **Personal Relevance**: Show how this connects to their world
- **Encouraging Tone**: Build confidence, not intimidation

### ANALOGY BANK (Choose What Fits)
- **Social situations**: Groups, clubs, relationships, teams
- **Games and sports**: Rules, strategies, fair play
- **Cooking**: Recipes, ingredients, combinations
- **Technology**: Apps, computers, networks
- **Nature**: Ecosystems, patterns, balance
- **Building things**: Construction, design, blueprints

## 📏 LENGTH TARGET
{% if config.verbosity == "concise" %}
**Concise Mode (150-250 words):**
- One powerful analogy
- Focus on the single most amazing insight
- Leave them wanting to know more
{% elif config.verbosity == "detailed" %}
**Detailed Mode (300-500 words):**
- Main analogy plus supporting examples
- Walk through the key idea step by step
- Include why mathematicians get excited about this
{% else %}
**Comprehensive Mode (500-800 words):**
- Multiple analogies for different perspectives
- Full story arc with context and implications
- Connections to other fascinating math topics
{% endif %}

## 🎨 STYLE REQUIREMENTS
- **Tone**: Conversational and enthusiastic, like talking to a curious friend
- **Perspective**: Use "you," "we," and "imagine" to include the reader
- **Questions**: Ask engaging questions that make them think
- **Surprise**: Include at least one "wait, really?" moment
- **Confidence**: Assume they're smart enough to get this (because they are!)

## 📝 RESPONSE FORMAT
Write your explanation as a single, flowing piece that feels like a conversation. No JSON needed - just pure, engaging storytelling that transforms mathematical fear into mathematical wonder.

## 🚀 REMEMBER
Your job isn't to dumb down the math - it's to unlock the door that shows how beautiful and logical mathematics really is. Every person has mathematical intuition; you're just helping them discover it.
"""
        return self.env.from_string(template_str)

    @property
    def tactic_explanation_template(self) -> Template:
        """Enhanced template for explaining Lean tactics with deep pedagogical insight."""
        template_str = """
You are a world-class Lean 4 instructor who has taught thousands of students to write formal proofs. Your expertise lies in breaking down tactical thinking into digestible, memorable patterns.

## 🎯 THE PROOF UNDER ANALYSIS
**Theorem:** {{ theorem_name }}
**Mathematical Statement:** {{ theorem_statement | format_statement }}
{% if proof_text %}
**Lean 4 Proof:**
```lean
{{ proof_text }}
```
{% endif %}
{% if dependencies %}**Required Knowledge:** {{ dependencies | format_dependencies }}{% endif %}
{% if mathematical_context %}**Mathematical Context:** {{ mathematical_context }}{% endif %}

## 🧠 TACTICAL THINKING FRAMEWORK
Great proof writers think in patterns. Here's how to analyze tactics like a pro:

### EXAMPLE: Tactical Analysis of "simp [one_mul, mul_one]"
**What it does:** Simplifies expressions using the given lemmas
**Why chosen:** Eliminates trivial cases so we can focus on the core logic
**When to use:** When you have obvious algebraic simplifications
**Common mistake:** Forgetting to include necessary lemmas in the simp call
**Pro tip:** Always check what simp actually simplified with "simp?"

## 🔍 YOUR TACTICAL ANALYSIS
Provide a {{ config.verbosity }} analysis covering:

### PHASE 1: TACTICAL INVENTORY
For each tactic used, identify:
- **Syntax**: How it appears in the proof
- **Purpose**: What mathematical goal it achieves
- **Context**: Why it appears at this specific point
- **Alternatives**: What other tactics could work here

### PHASE 2: STRATEGIC REASONING
- **Opening moves**: How does the proof start and why?
- **Core strategy**: What's the main tactical approach?
- **Clever moments**: Any particularly elegant tactic usage?
- **Potential pitfalls**: Where could things go wrong?

### PHASE 3: LEARNING PATTERNS
- **Tactic combinations**: Which tactics work well together?
- **Proof templates**: What general patterns emerge?
- **Mental models**: How to think about when to use each tactic?
- **Practice exercises**: What similar problems would build these skills?

## 🎓 PEDAGOGICAL LEVELS
{% if config.verbosity == "concise" %}
**Concise Mode**: Focus on the 2-3 most important tactics and their key insights
{% elif config.verbosity == "detailed" %}
**Detailed Mode**: Cover all major tactics with explanations and alternatives
{% else %}
**Comprehensive Mode**: Deep dive into tactical reasoning, patterns, and pedagogy
{% endif %}

## 📋 RESPONSE FORMAT
Structure your response as:

```markdown
# Tactical Analysis: {{ theorem_name }}

## 🚀 Proof Strategy Overview
[High-level description of the tactical approach]

## 🔧 Tactic-by-Tactic Breakdown
{% if proof_text %}
### Tactic 1: [Name]
- **Code:** `[exact syntax]`
- **Purpose:** [What it accomplishes]
- **Why here:** [Strategic reasoning]
- **Alternatives:** [Other options]
- **Learning note:** [Key insight for students]

[Continue for each major tactic...]
{% else %}
[Infer likely tactics from the theorem statement and mathematical context]
{% endif %}

## 🎯 Tactical Patterns
- **Opening pattern:** [How proofs like this typically start]
- **Core techniques:** [Main tactical approaches for this type of problem]
- **Finishing moves:** [How to close out the proof]

## 💡 Learning Insights
- **When to use:** [General principles for applying these tactics]
- **Common mistakes:** [What students typically get wrong]
- **Practice ideas:** [How to build intuition for these tactics]

## 🔄 Alternative Approaches
[Other tactical routes that could work, with trade-offs]
```

## 🎪 COMMUNICATION STYLE
- **Expert but approachable**: Like a patient mentor sharing hard-won insights
- **Pattern-focused**: Help students see the forest, not just the trees
- **Practical wisdom**: Include the kind of advice that comes from experience
- **Encouraging**: Build confidence in tactical reasoning
{% if config.include_reasoning %}
- **Reasoning-heavy**: Dive deep into the "why" behind each tactical choice
{% endif %}

## 🌟 REMEMBER
Your goal is to transform tactical confusion into tactical intuition. Help students develop the mental models that turn them into confident proof writers.
"""
        return self.env.from_string(template_str)

    @property
    def step_by_step_template(self) -> Template:
        """Enhanced template for detailed step-by-step proof walkthroughs with guided learning."""
        template_str = """
You are an exceptional mathematics tutor known for making complex proofs feel like guided adventures. Students often say you make them feel like mathematical detectives solving elegant puzzles.

## 🔍 THE MATHEMATICAL INVESTIGATION
**Case:** {{ theorem_name }}
**What We're Proving:** {{ theorem_statement | format_statement }}
{% if dependencies %}**Tools We'll Need:** {{ dependencies | format_dependencies }}{% endif %}
{% if docstring %}**Why This Matters:** {{ docstring }}{% endif %}
{% if mathematical_context %}**Mathematical Territory:** {{ mathematical_context }}{% endif %}
{% if proof_text %}
**Our Map (Formal Proof):**
```lean
{{ proof_text }}
```
{% endif %}

## 🎪 MASTERFUL TUTORING EXAMPLE
Watch how a great tutor guides a student through a proof step:

**Step 3 of "Proving commutativity":**
> "Okay, now we're at the crucial moment. We want to show that a * b = b * a. But look what we've set up in the previous steps - we have these two expressions that look different but are actually the same thing! 
> 
> Let's use the associative property here. Why? Because it's going to let us rearrange the parentheses in just the right way to reveal the symmetry we're looking for. Watch this magic happen..."
> 
> **[Shows the algebraic manipulation]**
> 
> "See how that works? The associative property acted like a key that unlocked the door to commutativity. This is the kind of move you'll use again and again in algebra!"

## 🎯 YOUR TUTORING MISSION
Create a {{ config.verbosity }} walkthrough that makes every student think "I can do this!"

### GUIDED DISCOVERY STRUCTURE
1. **Detective Setup**: What's our mystery to solve?
2. **Evidence Gathering**: What facts and tools do we have?
3. **Investigation Plan**: How will we crack this case?
4. **Step-by-Step Sleuthing**: Following the clues
5. **Case Closed**: Celebrating the solution

### STEP-BY-STEP EXCELLENCE
For each step, provide:

#### 🎬 THE SETUP
- **Where we are**: Current state of the proof
- **Where we're going**: What this step will achieve
- **Why now**: Why this is the right moment for this step

#### 🧠 THE THINKING
- **The idea**: What insight drives this step
- **The method**: How we'll execute the idea
- **The caution**: What could go wrong and how to avoid it

#### 🔧 THE EXECUTION
- **The math**: Detailed mathematical work
- **The checking**: How we verify this step is correct
- **The connection**: How this links to our overall strategy

#### 🎉 THE PAYOFF
- **What we gained**: Progress toward our goal
- **Why it's beautiful**: The elegant aspect of this step
- **What's next**: Setting up for the following step

## 🎓 TUTORING LEVELS
{% if config.verbosity == "concise" %}
**Concise Mode (3-5 key steps):**
- Focus on the most important logical moves
- Include the crucial insights that make everything click
- Perfect for someone who wants the essential flow
{% elif config.verbosity == "detailed" %}
**Detailed Mode (5-8 detailed steps):**
- Include all major logical steps with explanations
- Add common misconceptions and how to avoid them
- Great for someone learning to write similar proofs
{% else %}
**Comprehensive Mode (8-12 thorough steps):**
- Every significant move explained in detail
- Include alternative approaches and why we chose this one
- Add connections to broader mathematical principles
- Perfect for deep understanding and teaching others
{% endif %}

## 📚 RESPONSE FORMAT
Structure as a guided journey:

```markdown
# Step-by-Step Proof Walkthrough: {{ theorem_name }}

## 🎯 The Challenge
[What exactly are we trying to prove and why it's interesting]

## 🧭 Our Strategy  
[The high-level game plan - how we'll tackle this proof]

## 🔍 The Investigation

### Step 1: [Engaging Title]
**🎬 Setup:** [Where we are and where we're heading]
**🧠 Key Insight:** [The main idea driving this step]
**🔧 The Work:** [Detailed mathematical content]
**✅ Check:** [How we know this step is correct]
**➡️ Next:** [How this enables the following step]

[Continue for each step...]

## 🎊 Victory Celebration
[Wrapping up - what we proved and why it's beautiful]

## 🔗 Connections
[How this proof connects to bigger mathematical ideas]
```

## 🎭 TEACHING PERSONALITY
- **Encouraging coach**: Build confidence with every step
- **Patient guide**: Never rush, always explain
- **Enthusiastic explorer**: Show genuine excitement for the mathematics
- **Careful mentor**: Point out pitfalls and how to avoid them
- **Wisdom sharer**: Include insights that come from experience

## 🌟 GOLDEN RULE
Never let a student feel lost. Every step should feel like a natural, logical progression where they can think "Of course! That makes perfect sense!"
"""
        return self.env.from_string(template_str)

    @property
    def mathematical_context_template(self) -> Template:
        """Template for generating rich mathematical context and connections."""
        template_str = """
You are a mathematical historian and theorist with deep knowledge across all areas of mathematics. Your specialty is revealing the beautiful connections between mathematical concepts and their historical development.

## 🔬 THE MATHEMATICAL SPECIMEN
**Theorem:** {{ theorem_name }}
**Statement:** {{ theorem_statement | format_statement }}
{% if dependencies %}**Direct Dependencies:** {{ dependencies | format_dependencies }}{% endif %}
{% if docstring %}**Immediate Context:** {{ docstring }}{% endif %}

## 🎯 MISSION: MATHEMATICAL CARTOGRAPHY
Create a rich mathematical context that reveals how this theorem fits into the grand tapestry of mathematics.

### HISTORICAL PERSPECTIVE
- **Timeline**: When was this type of result first discovered/formalized?
- **Key figures**: Who were the mathematical pioneers in this area?
- **Motivation**: What practical or theoretical problems led to this development?
- **Evolution**: How has understanding of this concept evolved over time?

### MATHEMATICAL ECOLOGY
- **Field classification**: What mathematical discipline(s) does this belong to?
- **Fundamental concepts**: What core mathematical ideas does it build upon?
- **Proof techniques**: What are the standard approaches for results like this?
- **Generalizations**: How does this fit into more general theoretical frameworks?

### CONNECTION WEB
- **Prerequisites**: What mathematical background is truly essential?
- **Applications**: Where does this theorem get used in practice?
- **Related results**: What other theorems are in the same "family"?
- **Future directions**: What deeper results does this enable or point toward?

### CONCEPTUAL LANDSCAPE
- **Analogies**: What simpler or more familiar concepts mirror this one?
- **Intuition sources**: Where does mathematical intuition for this come from?
- **Common misconceptions**: What do people typically get wrong about this area?
- **Beauty factors**: What makes this mathematically elegant or surprising?

## 📊 RESPONSE FORMAT
Provide a comprehensive mathematical context analysis:

```json
{
  "mathematical_context": {
    "primary_field": "The main mathematical discipline",
    "subfields": ["relevant", "mathematical", "subfields"],
    "abstraction_level": "concrete|intermediate|abstract",
    "historical_context": {
      "era": "When this type of mathematics was developed",
      "key_mathematicians": ["important", "historical", "figures"],
      "original_motivation": "What problems led to this development",
      "modern_perspective": "How we view this area today"
    },
    "conceptual_foundations": {
      "core_concepts": ["fundamental", "mathematical", "ideas"],
      "proof_paradigms": ["common", "proof", "techniques"],
      "mental_models": ["ways", "to", "think", "about", "this"],
      "common_patterns": ["recurring", "mathematical", "themes"]
    },
    "mathematical_connections": {
      "prerequisites": [
        {
          "concept": "Essential background concept",
          "why_needed": "How it's used in understanding this theorem",
          "depth_required": "Surface familiarity|Working knowledge|Deep understanding"
        }
      ],
      "related_theorems": [
        {
          "theorem": "Related result",
          "relationship": "How they connect",
          "comparison": "Similarities and differences"
        }
      ],
      "applications": [
        {
          "area": "Where it's applied",
          "how_used": "Specific role in applications",
          "importance": "Why it matters there"
        }
      ]
    },
    "pedagogical_insights": {
      "intuition_sources": ["where", "intuition", "comes", "from"],
      "common_misconceptions": ["typical", "student", "errors"],
      "learning_progression": "How to build understanding step by step",
      "analogies": [
        {
          "analogy": "Helpful comparison",
          "explanation": "How the analogy illuminates the concept",
          "limitations": "Where the analogy breaks down"
        }
      ]
    },
    "mathematical_significance": {
      "importance_level": "fundamental|important|specialized|niche",
      "beauty_factors": ["what", "makes", "this", "elegant"],
      "surprise_elements": ["unexpected", "or", "counterintuitive", "aspects"],
      "broader_impact": "How this influences other areas of mathematics"
    }
  }
}
```

## 🌟 EXCELLENCE CRITERIA
- **Accuracy**: All historical and mathematical information must be precise
- **Depth**: Go beyond surface-level connections to reveal deep patterns
- **Accessibility**: Explain complex ideas in ways that build understanding
- **Comprehensiveness**: Cover all major aspects of the mathematical landscape
- **Insight**: Provide perspectives that illuminate rather than just inform

Your analysis should make someone think: "Now I understand not just what this theorem says, but why it matters and how it fits into the beautiful structure of mathematics!"
"""
        return self.env.from_string(template_str)

    def get_template(self, generation_type: GenerationType) -> Template:
        """Get the appropriate template for a generation type."""
        template_map = {
            GenerationType.PROOF_SKETCH: self.proof_sketch_template,
            GenerationType.ELI5_EXPLANATION: self.eli5_template,
            GenerationType.TACTIC_EXPLANATION: self.tactic_explanation_template,
            GenerationType.STEP_BY_STEP: self.step_by_step_template,
            GenerationType.MATHEMATICAL_CONTEXT: self.mathematical_context_template,
        }

        template = template_map.get(generation_type)
        if template is None:
            raise ValueError(
                f"No template found for generation type: {generation_type}"
            )

        return template

    def render_prompt(
        self,
        generation_type: GenerationType,
        theorem_name: str,
        theorem_statement: str,
        config: GenerationConfig,
        dependencies: Optional[List[str]] = None,
        proof_text: Optional[str] = None,
        docstring: Optional[str] = None,
        mathematical_context: Optional[str] = None,
    ) -> str:
        """Render a prompt template with the given parameters."""
        template = self.get_template(generation_type)

        return template.render(
            theorem_name=theorem_name,
            theorem_statement=theorem_statement,
            config=config,
            dependencies=dependencies or [],
            proof_text=proof_text,
            docstring=docstring,
            mathematical_context=mathematical_context,
        )


# Global instance for easy access
prompt_templates = PromptTemplates()


def render_proof_sketch_prompt(
    theorem: TheoremInfo,
    config: GenerationConfig,
    mathematical_context: Optional[str] = None,
) -> str:
    """Convenience function to render proof sketch prompt."""
    return prompt_templates.render_prompt(
        generation_type=GenerationType.PROOF_SKETCH,
        theorem_name=theorem.name,
        theorem_statement=theorem.statement,
        config=config,
        dependencies=theorem.dependencies,
        proof_text=theorem.proof,
        docstring=theorem.docstring,
        mathematical_context=mathematical_context,
    )


def render_eli5_prompt(
    theorem: TheoremInfo,
    config: GenerationConfig,
    mathematical_context: Optional[str] = None,
) -> str:
    """Convenience function to render ELI5 prompt."""
    return prompt_templates.render_prompt(
        generation_type=GenerationType.ELI5_EXPLANATION,
        theorem_name=theorem.name,
        theorem_statement=theorem.statement,
        config=config,
        dependencies=theorem.dependencies,
        proof_text=theorem.proof,
        docstring=theorem.docstring,
        mathematical_context=mathematical_context,
    )


def render_tactic_explanation_prompt(
    theorem: TheoremInfo,
    config: GenerationConfig,
    mathematical_context: Optional[str] = None,
) -> str:
    """Convenience function to render tactic explanation prompt."""
    return prompt_templates.render_prompt(
        generation_type=GenerationType.TACTIC_EXPLANATION,
        theorem_name=theorem.name,
        theorem_statement=theorem.statement,
        config=config,
        dependencies=theorem.dependencies,
        proof_text=theorem.proof,
        docstring=theorem.docstring,
        mathematical_context=mathematical_context,
    )


def render_step_by_step_prompt(
    theorem: TheoremInfo,
    config: GenerationConfig,
    mathematical_context: Optional[str] = None,
) -> str:
    """Convenience function to render step-by-step prompt."""
    return prompt_templates.render_prompt(
        generation_type=GenerationType.STEP_BY_STEP,
        theorem_name=theorem.name,
        theorem_statement=theorem.statement,
        config=config,
        dependencies=theorem.dependencies,
        proof_text=theorem.proof,
        docstring=theorem.docstring,
        mathematical_context=mathematical_context,
    )


def render_mathematical_context_prompt(
    theorem: TheoremInfo,
    config: GenerationConfig,
    mathematical_context: Optional[str] = None,
) -> str:
    """Convenience function to render mathematical context prompt."""
    return prompt_templates.render_prompt(
        generation_type=GenerationType.MATHEMATICAL_CONTEXT,
        theorem_name=theorem.name,
        theorem_statement=theorem.statement,
        config=config,
        dependencies=theorem.dependencies,
        proof_text=theorem.proof,
        docstring=theorem.docstring,
        mathematical_context=mathematical_context,
    )
