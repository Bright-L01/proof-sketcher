"""Setup script for Proof Sketcher."""

from pathlib import Path

from setuptools import find_packages, setup

# Read README for long description
readme_path = Path(__file__).parent / "README.md"
long_description = readme_path.read_text(encoding="utf-8") if readme_path.exists() else ""

setup(
    name="proof-sketcher",
    version="0.1.0",
    description="Transform Lean 4 theorems into natural language explanations with animations",
    long_description=long_description,
    long_description_content_type="text/markdown",
    author="Proof Sketcher Contributors",
    author_email="",
    url="https://github.com/your-org/proof-sketcher",
    license="MIT",

    # Package configuration
    package_dir={"": "src"},
    packages=find_packages(where="src"),
    include_package_data=True,
    package_data={
        "proof_sketcher": [
            "parser/*.lean",
            "templates/*.jinja2",
            "templates/**/*.jinja2",
        ],
    },

    # Python version requirement
    python_requires=">=3.9",

    # Dependencies
    install_requires=[
        "click>=8.0",
        "pydantic>=2.0",
        "rich>=13.0",
        "jinja2>=3.0",
        "PyYAML>=6.0",
        "toml>=0.10",
        "typing-extensions>=4.0",
        "tenacity>=8.0",
        "orjson>=3.8",
        "aiofiles>=23.0",
        "jsonschema>=4.0",
    ],

    # Optional dependencies
    extras_require={
        "dev": [
            "pytest>=7.0",
            "pytest-asyncio>=0.21",
            "pytest-cov>=4.0",
            "black>=23.0",
            "ruff>=0.1",
            "mypy>=1.0",
            "pre-commit>=3.0",
        ],
        "mcp": [
            "mcp>=0.1",  # For MCP server integration
        ],
        "pdf": [
            "reportlab>=4.0",  # For PDF generation
            "PyPDF2>=3.0",
        ],
        "jupyter": [
            "nbformat>=5.0",  # For Jupyter notebook export
            "nbconvert>=7.0",
        ],
    },

    # Entry points
    entry_points={
        "console_scripts": [
            "proof-sketcher=proof_sketcher.cli:cli",
        ],
    },

    # Classifiers
    classifiers=[
        "Development Status :: 3 - Alpha",
        "Intended Audience :: Developers",
        "Intended Audience :: Education",
        "Intended Audience :: Science/Research",
        "License :: OSI Approved :: MIT License",
        "Programming Language :: Python :: 3",
        "Programming Language :: Python :: 3.9",
        "Programming Language :: Python :: 3.10",
        "Programming Language :: Python :: 3.11",
        "Programming Language :: Python :: 3.12",
        "Topic :: Scientific/Engineering :: Mathematics",
        "Topic :: Software Development :: Documentation",
        "Topic :: Education",
        "Environment :: Console",
        "Operating System :: OS Independent",
    ],

    # Keywords
    keywords=[
        "lean4", "theorem", "proof", "mathematics", "animation",
        "documentation", "education", "formal-verification",
        "claude", "manim", "mathlib4"
    ],
)
