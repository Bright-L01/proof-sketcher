"""Project scanner for discovering and analyzing Lean files."""

import logging
import re
from pathlib import Path
from typing import Dict, List, Optional, Set, Tuple

import networkx as nx

# Validation imports removed - implement inline validation


class ProjectScanner:
    """Scan Lean projects and analyze dependencies."""

    def __init__(self, ignore_patterns: Optional[List[str]] = None):
        """Initialize project scanner.

        Args:
            ignore_patterns: List of glob patterns to ignore
        """
        self.logger = logging.getLogger(__name__)
        self.ignore_patterns = ignore_patterns or [
            "**/build/**",
            "**/.lake/**",
            "**/lakefile.lean",
            "**/test/**",
            "**/Test/**",
        ]

    def scan_project(self, project_dir: Path) -> Dict:
        """Scan entire Lean project.

        Args:
            project_dir: Root directory of the Lean project

        Returns:
            Dictionary containing:
            - files: List of Lean files
            - process_order: Topologically sorted processing order
            - file_theorems: Map of files to theorem names
            - dependency_graph: NetworkX directed graph
            - statistics: Project statistics
        """
        # Validate project directory
        if not project_dir or not Path(project_dir).exists():
            raise ValueError(f"Invalid project directory: {project_dir}")

        project_dir = Path(project_dir).resolve()
        self.logger.info(f"Scanning project: {project_dir}")

        # Find all Lean files
        lean_files = self._find_lean_files(project_dir)
        self.logger.info(f"Found {len(lean_files)} Lean files")

        # Build dependency graph
        dep_graph = nx.DiGraph()
        file_imports = {}
        file_theorems = {}

        for lean_file in lean_files:
            rel_path = lean_file.relative_to(project_dir)
            dep_graph.add_node(str(rel_path))

            # Extract imports
            imports = self._extract_imports(lean_file, project_dir)
            file_imports[str(rel_path)] = imports

            for imp in imports:
                if imp in [str(f.relative_to(project_dir)) for f in lean_files]:
                    dep_graph.add_edge(imp, str(rel_path))

            # Extract theorem names
            theorems = self._extract_theorem_names(lean_file)
            file_theorems[str(rel_path)] = theorems

        # Determine processing order
        process_order = self._compute_processing_order(dep_graph, lean_files, project_dir)

        # Compute statistics
        statistics = self._compute_statistics(
            lean_files, file_theorems, dep_graph, project_dir
        )

        return {
            "project_dir": str(project_dir),
            "files": [str(f.relative_to(project_dir)) for f in lean_files],
            "process_order": process_order,
            "file_theorems": file_theorems,
            "file_imports": file_imports,
            "dependency_graph": dep_graph,
            "statistics": statistics,
        }

    def _find_lean_files(self, project_dir: Path) -> List[Path]:
        """Find all Lean files in project, respecting ignore patterns.

        Args:
            project_dir: Project root directory

        Returns:
            List of Lean file paths
        """
        lean_files = []

        for pattern in ["**/*.lean"]:
            for file_path in project_dir.rglob(pattern):
                # Check ignore patterns
                should_ignore = False
                for ignore_pattern in self.ignore_patterns:
                    if file_path.match(ignore_pattern):
                        should_ignore = True
                        break

                if not should_ignore:
                    lean_files.append(file_path)

        return sorted(lean_files)

    def _extract_imports(self, lean_file: Path, project_dir: Path) -> List[str]:
        """Extract import statements from Lean file.

        Args:
            lean_file: Path to Lean file
            project_dir: Project root directory

        Returns:
            List of imported module paths (relative to project)
        """
        try:
            content = lean_file.read_text(encoding="utf-8")
        except Exception as e:
            self.logger.warning(f"Failed to read {lean_file}: {e}")
            return []

        imports = []
        import_pattern = re.compile(r"^\s*import\s+(\S+)", re.MULTILINE)

        for match in import_pattern.finditer(content):
            module_name = match.group(1)

            # Convert module name to file path
            # e.g., "Mathlib.Data.List.Basic" -> "Mathlib/Data/List/Basic.lean"
            file_path = module_name.replace(".", "/") + ".lean"

            # Check if this maps to an actual file in the project
            full_path = project_dir / file_path
            if full_path.exists():
                imports.append(file_path)
            else:
                # Try without the first component (e.g., for local imports)
                parts = file_path.split("/", 1)
                if len(parts) > 1:
                    local_path = parts[1]
                    if (project_dir / local_path).exists():
                        imports.append(local_path)

        return imports

    def _extract_theorem_names(self, lean_file: Path) -> List[str]:
        """Extract theorem names from Lean file.

        Args:
            lean_file: Path to Lean file

        Returns:
            List of theorem names
        """
        try:
            content = lean_file.read_text(encoding="utf-8")
        except Exception as e:
            self.logger.warning(f"Failed to read {lean_file}: {e}")
            return []

        theorem_names = []

        # Patterns for different theorem-like declarations
        patterns = [
            re.compile(r"^\s*theorem\s+(\w+)", re.MULTILINE),
            re.compile(r"^\s*lemma\s+(\w+)", re.MULTILINE),
            re.compile(r"^\s*proposition\s+(\w+)", re.MULTILINE),
            re.compile(r"^\s*corollary\s+(\w+)", re.MULTILINE),
        ]

        for pattern in patterns:
            for match in pattern.finditer(content):
                theorem_name = match.group(1)
                if theorem_name and not theorem_name.startswith("_"):
                    theorem_names.append(theorem_name)

        return theorem_names

    def _compute_processing_order(
        self, dep_graph: nx.DiGraph, lean_files: List[Path], project_dir: Path
    ) -> List[str]:
        """Compute optimal processing order based on dependencies.

        Args:
            dep_graph: Dependency graph
            lean_files: List of all Lean files
            project_dir: Project root directory

        Returns:
            List of file paths in processing order
        """
        try:
            # Try topological sort
            process_order = list(nx.topological_sort(dep_graph))
            self.logger.info("Dependencies form a DAG - using topological order")
        except nx.NetworkXUnfeasible:
            # Cycles in dependencies
            self.logger.warning("Circular dependencies detected")

            # Find strongly connected components
            sccs = list(nx.strongly_connected_components(dep_graph))
            self.logger.info(f"Found {len(sccs)} strongly connected components")

            # Process SCCs in topological order of the condensation
            condensation = nx.condensation(dep_graph, scc=sccs)
            scc_order = nx.topological_sort(condensation)

            process_order = []
            for scc_idx in scc_order:
                # Add files from this SCC
                scc_files = sorted(sccs[scc_idx])
                process_order.extend(scc_files)

        return process_order

    def _compute_statistics(
        self, lean_files: List[Path], file_theorems: Dict, dep_graph: nx.DiGraph, project_dir: Path
    ) -> Dict:
        """Compute project statistics.

        Args:
            lean_files: List of Lean files
            file_theorems: Map of files to theorems
            dep_graph: Dependency graph
            project_dir: Project root directory

        Returns:
            Dictionary of statistics
        """
        total_theorems = sum(len(theorems) for theorems in file_theorems.values())
        total_lines = 0

        for lean_file in lean_files:
            try:
                content = lean_file.read_text(encoding="utf-8")
                total_lines += len(content.splitlines())
            except:
                pass

        # Analyze graph structure
        num_nodes = dep_graph.number_of_nodes()
        num_edges = dep_graph.number_of_edges()
        is_dag = nx.is_directed_acyclic_graph(dep_graph)

        # Find most connected files
        in_degrees = dict(dep_graph.in_degree())
        out_degrees = dict(dep_graph.out_degree())

        most_imported = sorted(in_degrees.items(), key=lambda x: x[1], reverse=True)[:5]
        most_importing = sorted(out_degrees.items(), key=lambda x: x[1], reverse=True)[:5]

        return {
            "total_files": len(lean_files),
            "total_theorems": total_theorems,
            "total_lines": total_lines,
            "avg_theorems_per_file": total_theorems / len(lean_files) if lean_files else 0,
            "dependency_graph": {
                "nodes": num_nodes,
                "edges": num_edges,
                "is_dag": is_dag,
                "density": nx.density(dep_graph),
            },
            "most_imported_files": most_imported,
            "most_importing_files": most_importing,
        }

    def analyze_file_complexity(self, lean_file: Path) -> Dict:
        """Analyze complexity metrics for a single file.

        Args:
            lean_file: Path to Lean file

        Returns:
            Dictionary of complexity metrics
        """
        try:
            content = lean_file.read_text(encoding="utf-8")
        except Exception as e:
            self.logger.warning(f"Failed to read {lean_file}: {e}")
            return {}

        lines = content.splitlines()
        
        # Count different elements
        theorems = len(re.findall(r"^\s*(?:theorem|lemma|proposition|corollary)\s+", content, re.MULTILINE))
        definitions = len(re.findall(r"^\s*(?:def|definition)\s+", content, re.MULTILINE))
        instances = len(re.findall(r"^\s*instance\s+", content, re.MULTILINE))
        structures = len(re.findall(r"^\s*(?:structure|class|inductive)\s+", content, re.MULTILINE))
        
        # Estimate proof complexity
        tactics = len(re.findall(r"\b(?:by|begin|calc|have|show|suffices)\b", content))
        
        return {
            "lines_of_code": len(lines),
            "theorems": theorems,
            "definitions": definitions,
            "instances": instances,
            "structures": structures,
            "tactics_used": tactics,
            "complexity_score": theorems * 3 + definitions * 2 + instances + structures,
        }

    def find_theorem_dependencies(self, project_data: Dict, theorem_name: str) -> Set[str]:
        """Find all theorems that a given theorem depends on.

        Args:
            project_data: Project scan data
            theorem_name: Name of theorem to analyze

        Returns:
            Set of theorem names that the given theorem depends on
        """
        dependencies = set()
        
        # Find which file contains the theorem
        containing_file = None
        for file_path, theorems in project_data["file_theorems"].items():
            if theorem_name in theorems:
                containing_file = file_path
                break
        
        if not containing_file:
            return dependencies
        
        # Get all files this file imports (transitively)
        dep_graph = project_data["dependency_graph"]
        imported_files = nx.ancestors(dep_graph, containing_file)
        imported_files.add(containing_file)  # Include the file itself
        
        # Collect all theorems from imported files
        for file_path in imported_files:
            if file_path in project_data["file_theorems"]:
                dependencies.update(project_data["file_theorems"][file_path])
        
        # Remove the theorem itself
        dependencies.discard(theorem_name)
        
        return dependencies