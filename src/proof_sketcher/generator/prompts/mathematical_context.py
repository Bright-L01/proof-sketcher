"""Mathematical context template for comprehensive background information."""

from .base import PromptBase


class MathematicalContextTemplate(PromptBase):
    """Template for generating rich mathematical context and connections."""

    def get_template_string(self) -> str:
        """Template for mathematical context generation."""
        return """
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
      "proof_paradigms": ["common", "proo", "techniques"],
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
