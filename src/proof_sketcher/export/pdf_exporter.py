"""PDF format exporter for theorem documentation.

This module exports theorems to PDF format using LaTeX as an
intermediate format. Requires a LaTeX distribution to be installed.
"""

import logging
import shutil
import subprocess
import tempfile
from datetime import datetime
from pathlib import Path
from typing import Optional

from .base_exporter import BaseExporter
from ..core.alpha_warning import ALPHA_VERSION
from ..parser.models import TheoremInfo


class PDFExporter(BaseExporter):
    """Export to PDF format via LaTeX."""

    def __init__(self):
        """Initialize PDF exporter."""
        super().__init__()
        self.logger = logging.getLogger(__name__)
        self.latex_available = self._check_latex()

    def _check_latex(self) -> bool:
        """Check if LaTeX is available."""
        try:
            result = subprocess.run(
                ["pdflatex", "--version"],
                capture_output=True,
                text=True,
                timeout=5,
            )
            return result.returncode == 0
        except (subprocess.SubprocessError, FileNotFoundError):
            self.logger.warning("LaTeX not available, PDF export will fail")
            return False

    def export(
        self,
        theorem: TheoremInfo,
        explanation: str,
        visualization: Optional[Path],
        output_path: Path,
    ) -> Path:
        """Export theorem to PDF format.

        Args:
            theorem: Theorem information
            explanation: Natural language explanation
            visualization: Path to visualization file
            output_path: Where to save the PDF

        Returns:
            Path to exported PDF file

        Raises:
            RuntimeError: If LaTeX is not available
        """
        if not self.latex_available:
            raise RuntimeError(
                "LaTeX is not available. Please install a LaTeX distribution "
                "to enable PDF export."
            )

        self._ensure_output_dir(output_path)

        # Create LaTeX content
        latex_content = self._create_latex(theorem, explanation, visualization)

        # Compile to PDF
        with tempfile.TemporaryDirectory() as temp_dir:
            temp_path = Path(temp_dir)

            # Write LaTeX file
            tex_file = temp_path / "theorem.tex"
            tex_file.write_text(latex_content, encoding="utf-8")

            # Copy visualization if needed
            if visualization and visualization.exists():
                if visualization.suffix in [".png", ".jpg", ".jpeg"]:
                    shutil.copy2(visualization, temp_path / visualization.name)

            # Compile LaTeX
            try:
                # Run pdflatex twice for proper references
                for _ in range(2):
                    result = subprocess.run(
                        [
                            "pdflatex",
                            "-interaction=nonstopmode",
                            "-output-directory",
                            str(temp_path),
                            str(tex_file),
                        ],
                        capture_output=True,
                        text=True,
                        timeout=30,
                    )

                # Check if PDF was created
                pdf_file = temp_path / "theorem.pdf"
                if pdf_file.exists():
                    shutil.copy2(pdf_file, output_path)
                    return output_path
                else:
                    raise RuntimeError(f"PDF compilation failed: {result.stderr}")

            except subprocess.TimeoutExpired:
                raise RuntimeError("LaTeX compilation timed out")
            except Exception as e:
                raise RuntimeError(f"PDF export failed: {e}")

    def _create_latex(
        self,
        theorem: TheoremInfo,
        explanation: str,
        visualization: Optional[Path],
    ) -> str:
        """Create LaTeX document content.

        Args:
            theorem: Theorem information
            explanation: Natural language explanation
            visualization: Path to visualization

        Returns:
            LaTeX document as string
        """

        # Escape special LaTeX characters
        def escape_latex(text: str) -> str:
            replacements = {
                "\\": "\\textbackslash{}",
                "{": "\\{",
                "}": "\\}",
                "_": "\\_",
                "^": "\\textasciicircum{}",
                "&": "\\&",
                "%": "\\%",
                "$": "\\$",
                "#": "\\#",
                "~": "\\textasciitilde{}",
            }
            for char, replacement in replacements.items():
                text = text.replace(char, replacement)
            return text

        theorem_name = escape_latex(theorem.name)
        theorem_statement = escape_latex(theorem.statement)
        explanation_escaped = escape_latex(explanation)

        latex = (
            r"""\documentclass[11pt,a4paper]{article}
\usepackage[utf8]{inputenc}
\usepackage[T1]{fontenc}
\usepackage{amsmath,amssymb,amsthm}
\usepackage{graphicx}
\usepackage{hyperref}
\usepackage{listings}
\usepackage{xcolor}
\usepackage{geometry}
\usepackage{fancybox}

\geometry{margin=1in}

\definecolor{leangreen}{RGB}{30,126,52}
\definecolor{alphawarning}{RGB}{255,243,205}
\lstdefinestyle{lean}{
    basicstyle=\ttfamily\small,
    keywordstyle=\color{leangreen}\bfseries,
    commentstyle=\color{gray},
    stringstyle=\color{red},
    numbers=left,
    numberstyle=\tiny\color{gray},
    stepnumber=1,
    frame=single,
    breaklines=true
}

\title{"""
            + theorem_name
            + r"""}
\author{Generated by Proof Sketcher}
\date{"""
            + datetime.now().strftime("%B %d, %Y")
            + r"""}

\begin{document}

\maketitle

\colorbox{alphawarning}{%
\begin{minipage}{\textwidth}
\textbf{⚠ Alpha Software Warning}\\
This documentation was generated by experimental software (v"""
            + ALPHA_VERSION
            + r""").\\
Output may be incorrect or incomplete.
\end{minipage}
}

\section{Statement}

\begin{lstlisting}[style=lean]
"""
            + theorem_statement
            + r"""
\end{lstlisting}

\section{Explanation}

"""
            + explanation_escaped
        )

        # Add visualization if available
        if visualization and visualization.suffix in [".png", ".jpg", ".jpeg"]:
            latex += (
                r"""

\section{Visualization}

\begin{figure}[h]
\centering
\includegraphics[width=0.8\textwidth]{"""
                + visualization.name
                + r"""}
\caption{Proof visualization}
\end{figure}
"""
            )

        latex += (
            r"""

\vfill
\hrule
\vspace{0.5cm}
\small
\textit{Source:} \texttt{"""
            + escape_latex(str(theorem.file_path.name))
            + r"""} (lines """
            + str(theorem.start_line)
            + "-"
            + str(theorem.end_line)
            + r""")

\end{document}"""
        )

        return latex
