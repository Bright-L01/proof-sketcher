"""Lake facet integration for doc-gen4 educational plugin.

This module provides integration with Lake's build system to enhance
doc-gen4 documentation generation with educational content.
"""

import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from .module_processor import ModuleProcessor
from .template_engine import EducationalTemplateEngine


@dataclass
class LakeFacetConfig:
    """Configuration for Lake facet integration."""

    input_dir: Path
    output_dir: Path
    enable_educational: bool = True
    educational_levels: list[str] = None
    cache_dir: Path | None = None

    def __post_init__(self):
        if self.educational_levels is None:
            self.educational_levels = ["beginner", "intermediate", "advanced"]


class EducationalLakeFacet:
    """Lake facet integration for educational content generation."""

    def __init__(self, config: LakeFacetConfig):
        """Initialize the Lake facet integration.

        Args:
            config: Configuration for the facet
        """
        self.config = config
        self.module_processor = ModuleProcessor()
        self.template_engine = EducationalTemplateEngine()

        # Create output directories
        self.config.output_dir.mkdir(parents=True, exist_ok=True)
        if self.config.cache_dir:
            self.config.cache_dir.mkdir(parents=True, exist_ok=True)

    def process_module_docs(self, module_name: str) -> dict[str, Any]:
        """Process documentation for a single module.

        Args:
            module_name: Name of the module to process

        Returns:
            Processing results
        """
        # Find module JSON file
        module_json_path = self.config.input_dir / f"{module_name}.json"
        if not module_json_path.exists():
            return {"error": f"Module JSON not found: {module_json_path}"}

        try:
            # Load and enhance module JSON
            with open(module_json_path, encoding="utf-8") as f:
                module_json = json.load(f)

            enhanced_json = self.module_processor.enhance_module_json(module_json)

            # Generate educational HTML
            educational_html = self.template_engine.render_educational_module(
                enhanced_json
            )

            # Save enhanced JSON
            enhanced_json_path = self.config.output_dir / f"{module_name}_enhanced.json"
            with open(enhanced_json_path, "w", encoding="utf-8") as f:
                json.dump(enhanced_json, f, indent=2, ensure_ascii=False)

            # Save educational HTML
            educational_html_path = (
                self.config.output_dir / f"{module_name}_educational.html"
            )
            with open(educational_html_path, "w", encoding="utf-8") as f:
                f.write(educational_html)

            # Get processing statistics
            stats = self.module_processor.get_educational_stats(enhanced_json)

            return {
                "module_name": module_name,
                "enhanced_json_path": str(enhanced_json_path),
                "educational_html_path": str(educational_html_path),
                "stats": stats,
                "success": True,
            }

        except Exception as e:
            return {"module_name": module_name, "error": str(e), "success": False}

    def process_all_modules(self) -> dict[str, Any]:
        """Process all modules in the input directory.

        Returns:
            Processing results for all modules
        """
        results = {
            "processed_modules": [],
            "failed_modules": [],
            "total_modules": 0,
            "success_count": 0,
            "error_count": 0,
        }

        # Find all JSON files
        json_files = list(self.config.input_dir.glob("*.json"))
        results["total_modules"] = len(json_files)

        for json_file in json_files:
            module_name = json_file.stem
            result = self.process_module_docs(module_name)

            if result.get("success", False):
                results["processed_modules"].append(result)
                results["success_count"] += 1
            else:
                results["failed_modules"].append(result)
                results["error_count"] += 1

        return results

    def generate_educational_assets(self) -> None:
        """Generate CSS and JavaScript assets for educational content."""
        assets_dir = self.config.output_dir / "assets"
        self.template_engine.create_educational_assets(assets_dir)

    def create_educational_index(self, processing_results: dict[str, Any]) -> str:
        """Create an index page for educational content.

        Args:
            processing_results: Results from processing modules

        Returns:
            Path to the created index file
        """
        index_data = {
            "title": "Educational Lean 4 Documentation",
            "processed_modules": processing_results["processed_modules"],
            "stats": {
                "total_modules": processing_results["total_modules"],
                "success_count": processing_results["success_count"],
                "error_count": processing_results["error_count"],
            },
            "generated_at": processing_results.get("generated_at", "unknown"),
        }

        index_html = self._create_index_html(index_data)
        index_path = self.config.output_dir / "educational_index.html"

        with open(index_path, "w", encoding="utf-8") as f:
            f.write(index_html)

        return str(index_path)

    def _create_index_html(self, index_data: dict[str, Any]) -> str:
        """Create HTML for the educational index page.

        Args:
            index_data: Data for the index page

        Returns:
            HTML content
        """
        return f"""
<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>{index_data["title"]}</title>
    <link rel="stylesheet" href="assets/educational.css">
    <style>
        body {{
            font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, sans-serif;
            max-width: 1200px;
            margin: 0 auto;
            padding: 2rem;
            background-color: #f8f9fa;
        }}
        .header {{
            text-align: center;
            margin-bottom: 3rem;
            padding: 2rem;
            background: white;
            border-radius: 8px;
            box-shadow: 0 2px 4px rgba(0,0,0,0.1);
        }}
        .stats-grid {{
            display: grid;
            grid-template-columns: repeat(auto-fit, minmax(200px, 1fr));
            gap: 1rem;
            margin-bottom: 2rem;
        }}
        .stat-card {{
            background: white;
            padding: 1.5rem;
            border-radius: 8px;
            text-align: center;
            box-shadow: 0 2px 4px rgba(0,0,0,0.1);
        }}
        .stat-number {{
            font-size: 2rem;
            font-weight: bold;
            color: #3498db;
        }}
        .stat-label {{
            color: #6c757d;
            margin-top: 0.5rem;
        }}
        .modules-grid {{
            display: grid;
            grid-template-columns: repeat(auto-fit, minmax(300px, 1fr));
            gap: 1rem;
        }}
        .module-card {{
            background: white;
            padding: 1.5rem;
            border-radius: 8px;
            box-shadow: 0 2px 4px rgba(0,0,0,0.1);
            transition: transform 0.2s ease;
        }}
        .module-card:hover {{
            transform: translateY(-2px);
            box-shadow: 0 4px 8px rgba(0,0,0,0.15);
        }}
        .module-name {{
            font-size: 1.2rem;
            font-weight: bold;
            color: #2c3e50;
            margin-bottom: 0.5rem;
        }}
        .module-stats {{
            display: flex;
            justify-content: space-between;
            margin-top: 1rem;
            color: #6c757d;
            font-size: 0.9rem;
        }}
        .module-link {{
            display: inline-block;
            margin-top: 1rem;
            padding: 0.5rem 1rem;
            background: #3498db;
            color: white;
            text-decoration: none;
            border-radius: 4px;
            transition: background 0.2s ease;
        }}
        .module-link:hover {{
            background: #2980b9;
        }}
    </style>
</head>
<body>
    <div class="header">
        <h1>{index_data["title"]}</h1>
        <p>Enhanced documentation with progressive explanations for learners at all levels</p>
    </div>

    <div class="stats-grid">
        <div class="stat-card">
            <div class="stat-number">{index_data["stats"]["total_modules"]}</div>
            <div class="stat-label">Total Modules</div>
        </div>
        <div class="stat-card">
            <div class="stat-number">{index_data["stats"]["success_count"]}</div>
            <div class="stat-label">Successfully Processed</div>
        </div>
        <div class="stat-card">
            <div class="stat-number">{index_data["stats"]["error_count"]}</div>
            <div class="stat-label">Errors</div>
        </div>
    </div>

    <div class="modules-grid">
        {self._generate_module_cards(index_data["processed_modules"])}
    </div>

    <script src="assets/educational.js"></script>
</body>
</html>
        """

    def _generate_module_cards(self, modules: list[dict[str, Any]]) -> str:
        """Generate HTML cards for processed modules.

        Args:
            modules: List of processed module data

        Returns:
            HTML content for module cards
        """
        cards = []

        for module in modules:
            stats = module.get("stats", {})
            educational_html_path = Path(module["educational_html_path"]).name

            card_html = f"""
            <div class="module-card">
                <div class="module-name">{module["module_name"]}</div>
                <div class="module-stats">
                    <span>Declarations: {stats.get("total_declarations", 0)}</span>
                    <span>Educational: {stats.get("educational_declarations", 0)}</span>
                    <span>Coverage: {stats.get("educational_coverage", 0):.1f}%</span>
                </div>
                <a href="{educational_html_path}" class="module-link">View Educational Content</a>
            </div>
            """
            cards.append(card_html)

        return "\n".join(cards)


def create_lake_facet_script(output_path: Path) -> None:
    """Create a Lake facet script for integration.

    Args:
        output_path: Path to write the script
    """
    script_content = '''#!/usr/bin/env python3
"""Lake facet script for educational documentation generation."""

import sys
import json
from pathlib import Path

from proof_sketcher.docgen_plugin.lake_facet import EducationalLakeFacet, LakeFacetConfig

def main():
    """Main entry point for Lake facet."""
    if len(sys.argv) < 3:
        print("Usage: educational_facet.py <input_dir> <output_dir>")
        sys.exit(1)

    input_dir = Path(sys.argv[1])
    output_dir = Path(sys.argv[2])

    # Create configuration
    config = LakeFacetConfig(
        input_dir=input_dir,
        output_dir=output_dir,
        enable_educational=True
    )

    # Create facet instance
    facet = EducationalLakeFacet(config)

    # Process all modules
    results = facet.process_all_modules()

    # Generate assets
    facet.generate_educational_assets()

    # Create index
    index_path = facet.create_educational_index(results)

    # Print results
    print(f"Processed {results['success_count']} modules successfully")
    print(f"Failed to process {results['error_count']} modules")
    print(f"Educational index created at: {index_path}")

    # Return success/error code
    sys.exit(0 if results['error_count'] == 0 else 1)

if __name__ == "__main__":
    main()
'''

    with open(output_path, "w", encoding="utf-8") as f:
        f.write(script_content)

    # Make executable
    output_path.chmod(0o755)
