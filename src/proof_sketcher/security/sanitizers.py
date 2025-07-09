"""
Input sanitization utilities.
SECURITY: Functions to sanitize and clean user inputs.
"""

import html
import re
import unicodedata
from typing import Any, Dict, List, Optional, Union


class InputSanitizer:
    """
    Input sanitization utilities to prevent various injection attacks.

    SECURITY RATIONALE:
    - HTML escaping prevents XSS attacks
    - SQL escaping prevents SQL injection
    - Unicode normalization prevents Unicode-based attacks
    - Input length limits prevent DoS attacks
    """

    # Maximum input lengths
    MAX_TEXT_LENGTH = 10000
    MAX_NAME_LENGTH = 200
    MAX_DESCRIPTION_LENGTH = 5000

    # Dangerous HTML tags and attributes
    DANGEROUS_TAGS = {
        "script",
        "iframe",
        "object",
        "embed",
        "form",
        "input",
        "button",
        "textarea",
        "select",
        "option",
        "meta",
        "link",
        "style",
        "base",
        "applet",
        "bgsound",
        "frame",
        "frameset",
    }

    DANGEROUS_ATTRIBUTES = {
        "onclick",
        "onload",
        "onerror",
        "onmouseover",
        "onmouseout",
        "onfocus",
        "onblur",
        "onchange",
        "onsubmit",
        "onreset",
        "onkeydown",
        "onkeyup",
        "onkeypress",
        "javascript:",
        "vbscript:",
        "data:",
        "livescript:",
        "mocha:",
    }

    @staticmethod
    def sanitize_html(text: str, allow_basic_tags: bool = False) -> str:
        """
        Sanitize HTML content to prevent XSS attacks.

        Args:
            text: HTML text to sanitize
            allow_basic_tags: Whether to allow safe basic tags

        Returns:
            Sanitized HTML text
        """
        if not isinstance(text, str):
            return str(text)

        if len(text) > InputSanitizer.MAX_TEXT_LENGTH:
            text = text[: InputSanitizer.MAX_TEXT_LENGTH]

        # Normalize Unicode
        text = unicodedata.normalize("NFKC", text)

        if not allow_basic_tags:
            # Escape all HTML
            return html.escape(text, quote=True)

        # Allow only safe basic tags
        safe_tags = {"p", "br", "strong", "em", "u", "i", "b", "code", "pre"}

        # Remove dangerous tags and attributes
        # This is a simple approach - for production use a library like bleach
        for tag in InputSanitizer.DANGEROUS_TAGS:
            text = re.sub(f"</{tag}[^>]*>", "", text, flags=re.IGNORECASE)
            text = re.sub(f"<{tag}[^>]*>", "", text, flags=re.IGNORECASE)

        # Remove dangerous attributes
        for attr in InputSanitizer.DANGEROUS_ATTRIBUTES:
            text = re.sub(
                f"{attr}\\s*=\\s*[\"'][^\"']*[\"']", "", text, flags=re.IGNORECASE
            )

        # Remove javascript: and data: URLs
        text = re.sub(
            r'(href|src)\s*=\s*["\']?(javascript|data|vbscript):[^"\']*["\']?',
            "",
            text,
            flags=re.IGNORECASE,
        )

        return text

    @staticmethod
    def sanitize_text(text: str, max_length: Optional[int] = None) -> str:
        """
        Sanitize plain text input.

        Args:
            text: Text to sanitize
            max_length: Maximum allowed length

        Returns:
            Sanitized text
        """
        if not isinstance(text, str):
            text = str(text)

        # Normalize Unicode
        text = unicodedata.normalize("NFKC", text)

        # Remove control characters except whitespace
        text = "".join(
            char
            for char in text
            if unicodedata.category(char)[0] != "C" or char.isspace()
        )

        # Limit length
        if max_length is None:
            max_length = InputSanitizer.MAX_TEXT_LENGTH

        if len(text) > max_length:
            text = text[:max_length]

        # Trim whitespace
        text = text.strip()

        return text

    @staticmethod
    def sanitize_filename(filename: str) -> str:
        """
        Sanitize filename to prevent path traversal and filesystem issues.

        Args:
            filename: Filename to sanitize

        Returns:
            Safe filename
        """
        if not isinstance(filename, str):
            filename = str(filename)

        # Normalize Unicode
        filename = unicodedata.normalize("NFKC", filename)

        # Remove path separators and dangerous characters
        dangerous_chars = r'[<>:"/\\|?*\x00-\x1f]'
        filename = re.sub(dangerous_chars, "_", filename)

        # Remove leading/trailing dots and spaces
        filename = filename.strip(". ")

        # Limit length
        if len(filename) > InputSanitizer.MAX_NAME_LENGTH:
            name, ext = filename.rsplit(".", 1) if "." in filename else (filename, "")
            max_name_len = (
                InputSanitizer.MAX_NAME_LENGTH - len(ext) - 1
                if ext
                else InputSanitizer.MAX_NAME_LENGTH
            )
            filename = name[:max_name_len] + ("." + ext if ext else "")

        # Ensure not empty
        if not filename:
            filename = "untitled"

        # Check for Windows reserved names
        reserved_names = {
            "CON",
            "PRN",
            "AUX",
            "NUL",
            "COM1",
            "COM2",
            "COM3",
            "COM4",
            "COM5",
            "COM6",
            "COM7",
            "COM8",
            "COM9",
            "LPT1",
            "LPT2",
            "LPT3",
            "LPT4",
            "LPT5",
            "LPT6",
            "LPT7",
            "LPT8",
            "LPT9",
        }

        base_name = filename.split(".")[0].upper()
        if base_name in reserved_names:
            filename = f"safe_{filename}"

        return filename

    @staticmethod
    def sanitize_theorem_name(name: str) -> str:
        """
        Sanitize theorem names for safe use in code generation.

        Args:
            name: Theorem name to sanitize

        Returns:
            Sanitized theorem name
        """
        if not isinstance(name, str):
            name = str(name)

        # Normalize Unicode
        name = unicodedata.normalize("NFKC", name)

        # Keep only alphanumeric, underscore, and dot
        name = re.sub(r"[^a-zA-Z0-9_.]", "_", name)

        # Ensure starts with letter or underscore
        if name and not (name[0].isalpha() or name[0] == "_"):
            name = f"theorem_{name}"

        # Limit length
        if len(name) > InputSanitizer.MAX_NAME_LENGTH:
            name = name[: InputSanitizer.MAX_NAME_LENGTH]

        # Ensure not empty
        if not name:
            name = "unnamed_theorem"

        return name

    @staticmethod
    def sanitize_json_input(
        data: Any, max_depth: int = 10, current_depth: int = 0
    ) -> Any:
        """
        Recursively sanitize JSON-like data structures.

        Args:
            data: Data to sanitize
            max_depth: Maximum nesting depth allowed
            current_depth: Current recursion depth

        Returns:
            Sanitized data
        """
        if current_depth > max_depth:
            return "[MAX_DEPTH_EXCEEDED]"

        if isinstance(data, dict):
            sanitized = {}
            for key, value in data.items():
                # Sanitize key
                safe_key = InputSanitizer.sanitize_text(str(key), max_length=100)
                # Sanitize value
                safe_value = InputSanitizer.sanitize_json_input(
                    value, max_depth, current_depth + 1
                )
                sanitized[safe_key] = safe_value
            return sanitized

        elif isinstance(data, list):
            return [
                InputSanitizer.sanitize_json_input(item, max_depth, current_depth + 1)
                for item in data[:1000]  # Limit list size
            ]

        elif isinstance(data, str):
            return InputSanitizer.sanitize_text(data)

        elif isinstance(data, (int, float, bool, type(None))):
            return data

        else:
            # Convert unknown types to string and sanitize
            return InputSanitizer.sanitize_text(str(data))

    @staticmethod
    def sanitize_latex(latex: str) -> str:
        """
        Sanitize LaTeX content to prevent command injection.

        Args:
            latex: LaTeX content to sanitize

        Returns:
            Sanitized LaTeX
        """
        if not isinstance(latex, str):
            latex = str(latex)

        # Normalize Unicode
        latex = unicodedata.normalize("NFKC", latex)

        # Remove dangerous LaTeX commands
        dangerous_commands = [
            r"\\input",
            r"\\include",
            r"\\write",
            r"\\read",
            r"\\openin",
            r"\\openout",
            r"\\immediate",
            r"\\special",
            r"\\csname",
            r"\\expandafter",
            r"\\catcode",
            r"\\de",
            r"\\gde",
            r"\\ede",
            r"\\xde",
            r"\\let",
            r"\\futurelet",
        ]

        for cmd in dangerous_commands:
            latex = re.sub(cmd + r"\b", "", latex, flags=re.IGNORECASE)

        # Limit length
        if len(latex) > InputSanitizer.MAX_TEXT_LENGTH:
            latex = latex[: InputSanitizer.MAX_TEXT_LENGTH]

        return latex

    @staticmethod
    def sanitize_command_args(args: List[str]) -> List[str]:
        """
        Sanitize command line arguments.

        Args:
            args: List of command arguments

        Returns:
            Sanitized argument list
        """
        sanitized_args = []

        for arg in args[:100]:  # Limit number of arguments
            if not isinstance(arg, str):
                arg = str(arg)

            # Normalize Unicode
            arg = unicodedata.normalize("NFKC", arg)

            # Remove null bytes and control characters
            arg = "".join(char for char in arg if ord(char) >= 32 or char in "\t\n\r")

            # Limit length
            if len(arg) > 1000:
                arg = arg[:1000]

            sanitized_args.append(arg)

        return sanitized_args
