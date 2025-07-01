"""AI integration for natural language generation using subprocess."""

import json
import logging
import subprocess
import time
from typing import Iterator, Optional

from ..core.exceptions import (
    AIExecutableError,
    AITimeoutError,
    GeneratorError,
)
from ..core.interfaces import IGenerator
from ..parser.models import TheoremInfo
from .models import (
    GenerationConfig,
    GenerationRequest,
    GenerationResponse,
    GenerationType,
    ProofSketch,
    ProofStep,
)
from .prompts import prompt_templates

# Backward compatibility aliases
ClaudeError = GeneratorError
ClaudeExecutableError = AIExecutableError
ClaudeAPIError = GeneratorError
ClaudeTimeoutError = AITimeoutError


class AIGenerator(IGenerator):
    """Generator for natural language explanations using AI CLI tools."""

    def __init__(
        self,
        ai_executable: str = "claude",  # Still defaults to claude for compatibility
        default_config: Optional[GenerationConfig] = None,
    ):
        """Initialize the AI generator.

        Args:
            ai_executable: Path to the AI CLI executable
            default_config: Default generation configuration
        """
        self.ai_executable = ai_executable
        self.default_config = default_config or GenerationConfig()
        self.logger = logging.getLogger(__name__)

        # Validate AI tool is available
        if not self.check_ai_available():
            raise AIExecutableError(
                f"AI executable not found: {ai_executable}",
                details={"executable": ai_executable},
                error_code="ai_executable_not_found",
            )

    def generate_proof_sketch(
        self,
        theorem: TheoremInfo,
        config: Optional[GenerationConfig] = None,
        mathematical_context: Optional[str] = None,
    ) -> ProofSketch:
        """Generate a structured proof sketch for a theorem.

        Args:
            theorem: Theorem information
            config: Generation configuration
            mathematical_context: Additional mathematical context

        Returns:
            ProofSketch with structured explanation

        Raises:
            ClaudeError: If generation fails
        """
        config = config or self.default_config

        # Create generation request
        request = GenerationRequest(
            generation_type=GenerationType.PROOF_SKETCH,
            theorem_name=theorem.name,
            theorem_statement=theorem.statement,
            theorem_dependencies=theorem.dependencies,
            proof_text=theorem.proof,
            docstring=theorem.docstring,
            mathematical_context=mathematical_context,
            config=config,
        )

        # Generate response
        response = self._generate_response(request)

        if not response.success:
            raise ClaudeAPIError(
                f"Failed to generate proof sketch: {response.error_message}"
            )

        # Parse the JSON response into ProofSketch
        if isinstance(response.content, str):
            try:
                # Extract JSON from response if it's wrapped in text
                content = response.content.strip()
                if content.startswith("```json"):
                    content = content.split("```json")[1].split("```")[0].strip()
                elif content.startswith("```"):
                    content = content.split("```")[1].split("```")[0].strip()

                sketch_data = json.loads(content)

                # Convert to ProofSketch model
                proof_sketch = ProofSketch(
                    theorem_name=sketch_data["theorem_name"],
                    introduction=sketch_data["introduction"],
                    key_steps=[
                        ProofStep(**step_data) for step_data in sketch_data["key_steps"]
                    ],
                    conclusion=sketch_data["conclusion"],
                    difficulty_level=sketch_data.get(
                        "difficulty_level", "intermediate"
                    ),
                    mathematical_areas=sketch_data.get("mathematical_areas", []),
                    prerequisites=sketch_data.get("prerequisites", []),
                )

                return proof_sketch

            except (json.JSONDecodeError, KeyError, TypeError) as e:
                self.logger.warning(f"Failed to parse proof sketch JSON: {e}")
                # Fallback: create a simple proof sketch from the text response
                return ProofSketch(
                    theorem_name=theorem.name,
                    introduction=response.content,
                    key_steps=[
                        ProofStep(
                            step_number=1,
                            description="See introduction for details",
                            mathematical_content=theorem.statement,
                            tactics=[],
                        )
                    ],
                    conclusion="Generated explanation above.",
                )

        # If response.content is already a ProofSketch
        if isinstance(response.content, ProofSketch):
            return response.content

        raise ClaudeAPIError("Unexpected response format for proof sketch")

    def generate_eli5_explanation(
        self,
        theorem: TheoremInfo,
        config: Optional[GenerationConfig] = None,
        mathematical_context: Optional[str] = None,
    ) -> str:
        """Generate an ELI5 (Explain Like I'm 5) explanation.

        Args:
            theorem: Theorem information
            config: Generation configuration
            mathematical_context: Additional mathematical context

        Returns:
            Plain text ELI5 explanation

        Raises:
            ClaudeError: If generation fails
        """
        config = config or self.default_config

        request = GenerationRequest(
            generation_type=GenerationType.ELI5_EXPLANATION,
            theorem_name=theorem.name,
            theorem_statement=theorem.statement,
            theorem_dependencies=theorem.dependencies,
            proof_text=theorem.proof,
            docstring=theorem.docstring,
            mathematical_context=mathematical_context,
            config=config,
        )

        response = self._generate_response(request)

        if not response.success:
            raise ClaudeAPIError(
                f"Failed to generate ELI5 explanation: {response.error_message}"
            )

        if isinstance(response.content, str):
            return response.content

        raise ClaudeAPIError("Unexpected response format for ELI5 explanation")

    def generate_tactic_explanation(
        self,
        theorem: TheoremInfo,
        config: Optional[GenerationConfig] = None,
        mathematical_context: Optional[str] = None,
    ) -> str:
        """Generate explanation of Lean tactics used in the proof.

        Args:
            theorem: Theorem information
            config: Generation configuration
            mathematical_context: Additional mathematical context

        Returns:
            Plain text tactic explanation

        Raises:
            ClaudeError: If generation fails
        """
        config = config or self.default_config

        request = GenerationRequest(
            generation_type=GenerationType.TACTIC_EXPLANATION,
            theorem_name=theorem.name,
            theorem_statement=theorem.statement,
            theorem_dependencies=theorem.dependencies,
            proof_text=theorem.proof,
            docstring=theorem.docstring,
            mathematical_context=mathematical_context,
            config=config,
        )

        response = self._generate_response(request)

        if not response.success:
            raise ClaudeAPIError(
                f"Failed to generate tactic explanation: {response.error_message}"
            )

        if isinstance(response.content, str):
            return response.content

        raise ClaudeAPIError("Unexpected response format for tactic explanation")

    def generate_step_by_step(
        self,
        theorem: TheoremInfo,
        config: Optional[GenerationConfig] = None,
        mathematical_context: Optional[str] = None,
    ) -> str:
        """Generate detailed step-by-step proof walkthrough.

        Args:
            theorem: Theorem information
            config: Generation configuration
            mathematical_context: Additional mathematical context

        Returns:
            Plain text step-by-step explanation

        Raises:
            ClaudeError: If generation fails
        """
        config = config or self.default_config

        request = GenerationRequest(
            generation_type=GenerationType.STEP_BY_STEP,
            theorem_name=theorem.name,
            theorem_statement=theorem.statement,
            theorem_dependencies=theorem.dependencies,
            proof_text=theorem.proof,
            docstring=theorem.docstring,
            mathematical_context=mathematical_context,
            config=config,
        )

        response = self._generate_response(request)

        if not response.success:
            raise ClaudeAPIError(
                f"Failed to generate step-by-step explanation: {response.error_message}"
            )

        if isinstance(response.content, str):
            return response.content

        raise ClaudeAPIError("Unexpected response format for step-by-step explanation")

    def generate_streaming(
        self,
        theorem: TheoremInfo,
        generation_type: GenerationType,
        config: Optional[GenerationConfig] = None,
        mathematical_context: Optional[str] = None,
    ) -> Iterator[str]:
        """Generate response with streaming support.

        Args:
            theorem: Theorem information
            generation_type: Type of generation to perform
            config: Generation configuration
            mathematical_context: Additional mathematical context

        Yields:
            Chunks of generated text as they arrive

        Raises:
            ClaudeError: If generation fails
        """
        config = config or self.default_config
        config.stream = True  # Enable streaming

        request = GenerationRequest(
            generation_type=generation_type,
            theorem_name=theorem.name,
            theorem_statement=theorem.statement,
            theorem_dependencies=theorem.dependencies,
            proof_text=theorem.proof,
            docstring=theorem.docstring,
            mathematical_context=mathematical_context,
            config=config,
        )

        # Generate prompt
        prompt = prompt_templates.render_prompt(
            generation_type=request.generation_type,
            theorem_name=request.theorem_name,
            theorem_statement=request.theorem_statement,
            config=request.config,
            dependencies=request.theorem_dependencies,
            proof_text=request.proof_text,
            docstring=request.docstring,
            mathematical_context=request.mathematical_context,
        )

        # Build Claude command for streaming
        cmd = self._build_ai_command(request.config, stream=True)

        try:
            # Start subprocess with streaming
            process = subprocess.Popen(
                cmd,
                stdin=subprocess.PIPE,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
                bufsize=1,  # Line buffered
            )

            # Send prompt
            if process.stdin:
                process.stdin.write(prompt)
                process.stdin.close()

            # Yield output as it comes
            if process.stdout:
                for line in iter(process.stdout.readline, ""):
                    if line.strip():  # Skip empty lines
                        yield line.rstrip("\n")

                process.stdout.close()

            # Wait for completion and check for errors
            return_code = process.wait()

            if return_code != 0:
                stderr_output = (
                    process.stderr.read() if process.stderr else "Unknown error"
                )
                raise ClaudeAPIError(f"Claude command failed: {stderr_output}")

        except subprocess.SubprocessError as e:
            raise ClaudeAPIError(f"Failed to start Claude process: {e}") from e
        finally:
            if "process" in locals():
                process.terminate()

    def _generate_response(self, request: GenerationRequest) -> GenerationResponse:
        """Generate response for a given request.

        Args:
            request: Generation request

        Returns:
            Generation response
        """
        start_time = time.time()

        try:
            # Generate prompt
            prompt = prompt_templates.render_prompt(
                generation_type=request.generation_type,
                theorem_name=request.theorem_name,
                theorem_statement=request.theorem_statement,
                config=request.config,
                dependencies=request.theorem_dependencies,
                proof_text=request.proof_text,
                docstring=request.docstring,
                mathematical_context=request.mathematical_context,
            )

            # Call Claude subprocess
            output = self._call_ai(prompt, request.config)

            generation_time = (time.time() - start_time) * 1000

            return GenerationResponse(
                request=request,
                content=output,
                generation_time_ms=generation_time,
                success=True,
            )

        except ClaudeTimeoutError:
            # Re-raise timeout errors
            raise
        except Exception as e:
            generation_time = (time.time() - start_time) * 1000

            return GenerationResponse(
                request=request,
                content="",
                generation_time_ms=generation_time,
                success=False,
                error_message=str(e),
            )

    def _call_ai(self, prompt: str, config: GenerationConfig) -> str:
        """Call Claude subprocess with the given prompt and configuration.

        Args:
            prompt: Prompt to send to Claude
            config: Generation configuration

        Returns:
            Generated text response

        Raises:
            ClaudeError: If subprocess call fails
        """
        cmd = self._build_ai_command(config)

        try:
            # Calculate timeout (add buffer for subprocess overhead)
            timeout = 120  # Default 2 minutes
            if config.max_tokens > 4000:
                timeout = 180  # 3 minutes for longer responses

            result = subprocess.run(
                cmd, input=prompt, capture_output=True, text=True, timeout=timeout
            )

            if result.returncode != 0:
                error_msg = result.stderr.strip() if result.stderr else "Unknown error"
                raise ClaudeAPIError(f"Claude command failed: {error_msg}")

            return result.stdout.strip()

        except subprocess.TimeoutExpired:
            raise AITimeoutError(
                "AI request timed out",
                details={"timeout": timeout, "config": config.model_dump()},
                error_code="ai_timeout",
            ) from None
        except subprocess.SubprocessError as e:
            raise GeneratorError(
                f"Failed to call AI: {e}",
                details={"command": cmd, "error": str(e)},
                error_code="ai_call_failed",
            ) from e

    def _build_ai_command(
        self, config: GenerationConfig, stream: bool = False
    ) -> list[str]:
        """Build the Claude CLI command with configuration.

        Args:
            config: Generation configuration
            stream: Whether to enable streaming

        Returns:
            Command list for subprocess
        """
        cmd = [self.ai_executable]

        # Model selection
        cmd.extend(["-m", config.model.value])

        # Temperature
        cmd.extend(["-t", str(config.temperature)])

        # Max tokens
        cmd.extend(["--max-tokens", str(config.max_tokens)])

        # System message if provided
        if config.system_message:
            cmd.extend(["-s", config.system_message])

        # Stop sequences
        for stop_seq in config.stop_sequences:
            cmd.extend(["--stop", stop_seq])

        # Streaming
        if stream or config.stream:
            cmd.append("--stream")

        # Use prompt mode
        cmd.append("-p")

        return cmd

    def check_ai_available(self) -> bool:
        """Check if Claude executable is available.

        Returns:
            True if Claude is available, False otherwise
        """
        try:
            result = subprocess.run(
                [self.ai_executable, "--version"],
                capture_output=True,
                text=True,
                timeout=10,
            )
            return result.returncode == 0
        except (subprocess.SubprocessError, FileNotFoundError):
            return False

    def get_ai_version(self) -> Optional[str]:
        """Get Claude CLI version.

        Returns:
            Version string if available, None otherwise
        """
        try:
            result = subprocess.run(
                [self.ai_executable, "--version"],
                capture_output=True,
                text=True,
                timeout=10,
            )
            if result.returncode == 0:
                return result.stdout.strip()
        except (subprocess.SubprocessError, FileNotFoundError):
            pass
        return None

    def validate_setup(self) -> bool:
        """Validate that Claude is properly set up.

        Returns:
            True if setup is valid, False otherwise
        """
        try:
            if not self.check_ai_available():
                self.logger.error(f"Claude executable not found: {self.ai_executable}")
                return False

            # Test basic functionality with a simple prompt
            test_prompt = "Respond with exactly: 'Claude is working'"
            test_config = GenerationConfig.fast()

            try:
                response = self._call_ai(test_prompt, test_config)
                if "Claude is working" in response:
                    self.logger.info("Claude setup validation successful")
                    return True
                else:
                    self.logger.warning(f"Claude test response unexpected: {response}")
                    return False

            except Exception as e:
                self.logger.error(f"Claude test call failed: {e}")
                return False

        except Exception as e:
            self.logger.error(f"Claude setup validation failed: {e}")
            return False


# Backward compatibility alias
ClaudeGenerator = AIGenerator
