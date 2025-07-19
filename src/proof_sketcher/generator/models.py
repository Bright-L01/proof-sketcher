"""Models for natural language generation."""

import hashlib
from datetime import datetime
from enum import Enum
from typing import Any, ClassVar

from pydantic import BaseModel, Field, field_validator


class GenerationModel(str, Enum):
    """Available Claude models for generation."""

    CLAUDE_3_5_SONNET = "claude-3-5-sonnet-20241022"
    CLAUDE_3_5_HAIKU = "claude-3-5-haiku-20241022"
    CLAUDE_3_OPUS = "claude-3-opus-20240229"


class GenerationType(str, Enum):
    """Types of generation supported."""

    PROOF_SKETCH = "proof_sketch"
    ELI5_EXPLANATION = "eli5_explanation"
    TACTIC_EXPLANATION = "tactic_explanation"
    STEP_BY_STEP = "step_by_step"
    MATHEMATICAL_CONTEXT = "mathematical_context"


class EducationalLevel(str, Enum):
    """Educational complexity levels for the Proof Explanation Ladder."""
    
    INTUITIVE = "intuitive"      # Level 1: Why this theorem matters and what it means
    CONCEPTUAL = "conceptual"    # Level 2: What proof strategy we're using and why  
    BRIDGING = "bridging"        # Level 3: How informal reasoning maps to formal steps
    FORMAL = "formal"            # Level 4: Complete Lean 4 syntax with annotations


class ProofStrategy(str, Enum):
    """Common proof strategies in discrete mathematics."""
    
    INDUCTION = "induction"                    # Mathematical induction
    CONTRADICTION = "contradiction"           # Proof by contradiction (reductio ad absurdum)
    DIRECT = "direct"                        # Direct proof
    CASES = "cases"                          # Case analysis / proof by cases
    CONSTRUCTION = "construction"            # Constructive existential proof
    CONTRAPOSITIVE = "contrapositive"        # Proof by contrapositive


class ProofStep(BaseModel):
    """A single step in a proof sketch with educational levels."""

    step_number: int = Field(..., description="Step number in the proof")
    
    # Progressive explanations for different educational levels
    intuitive_explanation: str = Field(..., description="Level 1: Intuitive explanation of what this step does")
    conceptual_explanation: str = Field(..., description="Level 2: Conceptual explanation with strategy context")
    bridging_explanation: str = Field(..., description="Level 3: Bridge between informal and formal reasoning")
    formal_explanation: str = Field(..., description="Level 4: Complete formal explanation with syntax")
    
    # Technical details
    tactics: list[str] = Field(default_factory=list, description="Lean tactics used")
    mathematical_content: str = Field(..., description="Mathematical content of the step")
    lean_code: str | None = Field(None, description="Actual Lean 4 code for this step")

    class Config:
        """Pydantic configuration."""

        str_strip_whitespace = True
        
    def get_explanation(self, level: EducationalLevel) -> str:
        """Get explanation for the specified educational level."""
        explanations = {
            EducationalLevel.INTUITIVE: self.intuitive_explanation,
            EducationalLevel.CONCEPTUAL: self.conceptual_explanation,
            EducationalLevel.BRIDGING: self.bridging_explanation,
            EducationalLevel.FORMAL: self.formal_explanation,
        }
        return explanations[level]


class ProofSketch(BaseModel):
    """An educational proof sketch with progressive complexity levels."""

    theorem_name: str = Field(..., description="Name of the theorem")
    theorem_statement: str = Field(..., description="Formal statement of the theorem")
    
    # Progressive educational content
    intuitive_overview: str = Field(..., description="Level 1: Why this theorem matters and what it means")
    conceptual_overview: str = Field(..., description="Level 2: What proof strategy we're using and why")
    bridging_overview: str = Field(..., description="Level 3: How informal reasoning maps to formal steps")
    formal_overview: str = Field(..., description="Level 4: Complete formal context and setup")
    
    key_steps: list[ProofStep] = Field(..., description="Key steps in the proof")
    
    # Progressive conclusions
    intuitive_conclusion: str = Field(..., description="Level 1: Intuitive wrap-up")
    conceptual_conclusion: str = Field(..., description="Level 2: Strategic significance")
    bridging_conclusion: str = Field(..., description="Level 3: Connection to formal proof")
    formal_conclusion: str = Field(..., description="Level 4: Complete formal conclusion")

    # Educational metadata
    proof_strategy: ProofStrategy = Field(..., description="Primary proof strategy used")
    discrete_math_topic: str | None = Field(None, description="Specific discrete mathematics topic")
    difficulty_level: str = Field(
        "intermediate", description="Difficulty: beginner, intermediate, advanced"
    )
    mathematical_areas: list[str] = Field(
        default_factory=list, description="Areas of mathematics involved"
    )
    prerequisites: list[str] = Field(
        default_factory=list, description="Prerequisites to understand this proof"
    )

    @field_validator("difficulty_level")
    @classmethod
    def validate_difficulty(cls, v: str) -> str:
        """Validate difficulty level."""
        allowed = ["beginner", "intermediate", "advanced"]
        if v not in allowed:
            raise ValueError(f"Difficulty must be one of {allowed}")
        return v

    @property
    def total_steps(self) -> int:
        """Get total number of proof steps."""
        return len(self.key_steps)

    def get_step(self, step_number: int) -> ProofStep | None:
        """Get a specific proof step by number."""
        for step in self.key_steps:
            if step.step_number == step_number:
                return step
        return None
        
    def get_overview(self, level: EducationalLevel) -> str:
        """Get overview for the specified educational level."""
        overviews = {
            EducationalLevel.INTUITIVE: self.intuitive_overview,
            EducationalLevel.CONCEPTUAL: self.conceptual_overview,
            EducationalLevel.BRIDGING: self.bridging_overview,
            EducationalLevel.FORMAL: self.formal_overview,
        }
        return overviews[level]
        
    def get_conclusion(self, level: EducationalLevel) -> str:
        """Get conclusion for the specified educational level."""
        conclusions = {
            EducationalLevel.INTUITIVE: self.intuitive_conclusion,
            EducationalLevel.CONCEPTUAL: self.conceptual_conclusion,
            EducationalLevel.BRIDGING: self.bridging_conclusion,
            EducationalLevel.FORMAL: self.formal_conclusion,
        }
        return conclusions[level]

    class Config:
        """Pydantic configuration."""

        str_strip_whitespace = True


class GenerationConfig(BaseModel):
    """Configuration for Claude generation."""

    # Model settings
    model: GenerationModel = Field(
        GenerationModel.CLAUDE_3_5_SONNET, description="Claude model to use"
    )
    temperature: float = Field(
        0.7, ge=0.0, le=1.0, description="Generation temperature"
    )
    max_tokens: int = Field(
        4000, ge=1, le=8192, description="Maximum tokens to generate"
    )

    # Generation behavior
    stream: bool = Field(False, description="Whether to stream responses")
    include_reasoning: bool = Field(True, description="Include reasoning in responses")
    verbosity: str = Field(
        "detailed", description="Level of detail: concise, detailed, verbose"
    )

    # System and behavior
    system_message: str | None = Field(None, description="Custom system message")
    stop_sequences: list[str] = Field(
        default_factory=list, description="Stop sequences"
    )

    # Cache settings
    cache_responses: bool = Field(True, description="Whether to cache responses")
    cache_ttl_hours: int = Field(24, ge=1, description="Cache TTL in hours")

    @field_validator("verbosity")
    @classmethod
    def validate_verbosity(cls, v: str) -> str:
        """Validate verbosity level."""
        allowed = ["concise", "detailed", "verbose"]
        if v not in allowed:
            raise ValueError(f"Verbosity must be one of {allowed}")
        return v

    @classmethod
    def fast(cls) -> "GenerationConfig":
        """Create configuration optimized for speed."""
        return cls(
            model=GenerationModel.CLAUDE_3_5_HAIKU,
            temperature=0.3,
            max_tokens=2000,
            verbosity="concise",
            include_reasoning=False,
            stream=False,
            system_message=None,
            cache_responses=True,
            cache_ttl_hours=24,
        )

    @classmethod
    def detailed(cls) -> "GenerationConfig":
        """Create configuration optimized for detail."""
        return cls(
            model=GenerationModel.CLAUDE_3_5_SONNET,
            temperature=0.7,
            max_tokens=6000,
            verbosity="detailed",
            include_reasoning=True,
            stream=False,
            system_message=None,
            cache_responses=True,
            cache_ttl_hours=24,
        )

    @classmethod
    def creative(cls) -> "GenerationConfig":
        """Create configuration optimized for creativity."""
        return cls(
            model=GenerationModel.CLAUDE_3_OPUS,
            temperature=0.9,
            max_tokens=4000,
            verbosity="verbose",
            include_reasoning=True,
            stream=False,
            system_message=None,
            cache_responses=True,
            cache_ttl_hours=24,
        )


class GenerationRequest(BaseModel):
    """A request for natural language generation."""

    generation_type: GenerationType = Field(
        ..., description="Type of generation requested"
    )
    theorem_name: str = Field(..., description="Name of the theorem")
    theorem_statement: str = Field(..., description="Statement of the theorem")
    theorem_dependencies: list[str] = Field(
        default_factory=list, description="Theorem dependencies"
    )

    # Optional context
    proof_text: str | None = Field(None, description="Proof text if available")
    docstring: str | None = Field(None, description="Existing docstring if available")
    mathematical_context: str | None = Field(
        None, description="Additional mathematical context"
    )

    # Generation configuration
    config: GenerationConfig = Field(
        default_factory=GenerationConfig.fast, description="Generation configuration"
    )

    def get_cache_key(self) -> str:
        """Generate a cache key for this request."""
        # Create a hash of the key components
        content = (
            f"{self.generation_type.value}:{self.theorem_name}:{self.theorem_statement}"
        )
        if self.proof_text:
            content += f":{self.proof_text}"
        if self.mathematical_context:
            content += f":{self.mathematical_context}"

        # Include relevant config in cache key
        config_content = f"{self.config.model.value}:{self.config.temperature}:{self.config.verbosity}"
        content += f":{config_content}"

        return hashlib.sha256(content.encode()).hexdigest()

    class Config:
        """Pydantic configuration."""

        str_strip_whitespace = True


class GenerationResponse(BaseModel):
    """Response from natural language generation."""

    request: GenerationRequest = Field(..., description="Original request")
    content: str | ProofSketch = Field(..., description="Generated content")

    # Metadata
    generated_at: datetime = Field(
        default_factory=datetime.now, description="Generation timestamp"
    )
    generation_time_ms: float | None = Field(
        None, description="Generation time in milliseconds"
    )
    token_count: int | None = Field(None, description="Number of tokens generated")

    # Success/error information
    success: bool = Field(True, description="Whether generation was successful")
    error_message: str | None = Field(
        None, description="Error message if generation failed"
    )

    @property
    def cache_key(self) -> str:
        """Get cache key from the request."""
        return self.request.get_cache_key()

    @property
    def is_proof_sketch(self) -> bool:
        """Check if content is a ProofSketch."""
        return isinstance(self.content, ProofSketch)

    @property
    def is_text_response(self) -> bool:
        """Check if content is plain text."""
        return isinstance(self.content, str)

    def to_dict(self) -> dict[str, Any]:
        """Convert to dictionary for serialization."""
        result = self.dict()

        # Handle datetime serialization
        if isinstance(result["generated_at"], datetime):
            result["generated_at"] = result["generated_at"].isoformat()

        return result

    class Config:
        """Pydantic configuration."""

        arbitrary_types_allowed = True
        json_encoders: ClassVar = {datetime: lambda dt: dt.isoformat()}


class CacheEntry(BaseModel):
    """An entry in the generation cache."""

    cache_key: str = Field(..., description="Cache key")
    response: GenerationResponse = Field(..., description="Cached response")
    cached_at: datetime = Field(
        default_factory=datetime.now, description="Cache timestamp"
    )
    ttl_hours: int = Field(24, description="TTL in hours")

    @property
    def is_expired(self) -> bool:
        """Check if cache entry is expired."""
        from datetime import timedelta

        expiry_time = self.cached_at + timedelta(hours=self.ttl_hours)
        return datetime.now() > expiry_time

    class Config:
        """Pydantic configuration."""

        arbitrary_types_allowed = True
        json_encoders: ClassVar = {datetime: lambda dt: dt.isoformat()}
