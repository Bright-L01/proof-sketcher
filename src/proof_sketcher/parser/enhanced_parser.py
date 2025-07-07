"""Enhanced Lean 4 parser with support for extended language constructs.

This module extends the basic parser to support:
- Inductive types and their constructors
- Structures and their fields  
- Classes and instances
- Definitions and axioms
- Namespaces and sections
- Variables and universe declarations
- Attributes and metadata
"""

import re
import logging
from dataclasses import dataclass, field
from enum import Enum
from pathlib import Path
from typing import Dict, List, Optional, Set, Match

from .models import TheoremInfo


class LeanConstruct(str, Enum):
    """Types of Lean 4 language constructs."""
    THEOREM = "theorem"
    LEMMA = "lemma"
    DEFINITION = "def"
    INDUCTIVE = "inductive"
    STRUCTURE = "structure"
    CLASS = "class"
    INSTANCE = "instance"
    AXIOM = "axiom"
    NAMESPACE = "namespace"
    SECTION = "section"
    VARIABLE = "variable"
    UNIVERSE = "universe"
    OPEN = "open"
    IMPORT = "import"
    EXPORT = "export"
    EXAMPLE = "example"
    NONCOMPUTABLE = "noncomputable"


class LeanAttribute(str, Enum):
    """Common Lean 4 attributes."""
    SIMP = "simp"
    INSTANCE = "instance"
    REDUCIBLE = "reducible"
    IRREDUCIBLE = "irreducible"
    SEMIREDUCIBLE = "semireducible"
    INLINE = "inline"
    NOINLINE = "noinline"
    MACRO_INLINE = "macro_inline"
    EXTERN = "extern"
    EXPORT = "export"
    DEPRECATED = "deprecated"


@dataclass
class LeanDeclaration:
    """Base class for all Lean declarations."""
    construct_type: LeanConstruct
    name: str
    line_number: int
    raw_text: str
    namespace: Optional[str] = None
    attributes: List[LeanAttribute] = field(default_factory=list)
    docstring: Optional[str] = None
    visibility: str = "public"  # public, private, protected
    

@dataclass 
class LeanTheorem(LeanDeclaration):
    """Theorem or lemma declaration."""
    statement: str = ""
    proof: Optional[str] = None
    parameters: List[str] = field(default_factory=list)
    dependencies: List[str] = field(default_factory=list)
    tactics: List[str] = field(default_factory=list)
    
    def to_theorem_info(self) -> TheoremInfo:
        """Convert to TheoremInfo for compatibility."""
        return TheoremInfo(
            name=self.name,
            statement=self.statement,
            proof=self.proof,
            line_number=self.line_number,
            docstring=self.docstring,
            namespace=self.namespace,
            visibility=self.visibility,
            dependencies=self.dependencies,
            tactics=self.tactics,
            is_axiom=False
        )


@dataclass
class LeanInductive(LeanDeclaration):
    """Inductive type declaration."""
    parameters: List[str] = field(default_factory=list)
    type_signature: str = ""
    constructors: List[Dict[str, str]] = field(default_factory=list)
    derives: List[str] = field(default_factory=list)


@dataclass
class LeanStructure(LeanDeclaration):
    """Structure declaration."""
    parameters: List[str] = field(default_factory=list)
    extends: List[str] = field(default_factory=list)
    fields: List[Dict[str, str]] = field(default_factory=list)
    derives: List[str] = field(default_factory=list)


@dataclass
class LeanClass(LeanDeclaration):
    """Class declaration."""
    parameters: List[str] = field(default_factory=list)
    extends: List[str] = field(default_factory=list)
    fields: List[Dict[str, str]] = field(default_factory=list)


@dataclass
class LeanInstance(LeanDeclaration):
    """Instance declaration."""
    class_name: str = ""
    instance_type: str = ""
    parameters: List[str] = field(default_factory=list)
    proof: Optional[str] = None


@dataclass
class LeanDefinition(LeanDeclaration):
    """Definition declaration."""
    type_signature: str = ""
    parameters: List[str] = field(default_factory=list)
    body: Optional[str] = None
    is_noncomputable: bool = False


@dataclass
class LeanNamespace(LeanDeclaration):
    """Namespace declaration."""
    declarations: List[LeanDeclaration] = field(default_factory=list)
    imports: List[str] = field(default_factory=list)
    opens: List[str] = field(default_factory=list)


class EnhancedLeanParser:
    """Enhanced parser for Lean 4 with support for extended language constructs."""
    
    def __init__(self) -> None:
        self.logger = logging.getLogger(__name__)
        self.current_namespace: Optional[str] = None
        self.namespace_stack: List[str] = []
        self.open_namespaces: Set[str] = set()
        
        # Compile regex patterns for performance
        self._compile_patterns()
    
    def _compile_patterns(self) -> None:
        """Compile regex patterns for parsing different constructs."""
        
        # Basic construct patterns
        self.patterns = {
            'theorem': re.compile(r'^(theorem|lemma)\s+(\w+)(?:\s*[:\(]|$)'),
            'definition': re.compile(r'^def\s+(\w+)(?:\s*[:\(]|$)'),
            'inductive': re.compile(r'^inductive\s+(\w+)(?:\s*[:\(]|$)'),
            'structure': re.compile(r'^structure\s+(\w+)(?:\s*[:\(]|$)'),
            'class': re.compile(r'^class\s+(\w+)(?:\s*[:\(]|$)'),
            'instance': re.compile(r'^instance(?:\s+(\w+))?\s*[:\[]'),
            'axiom': re.compile(r'^axiom\s+(\w+)(?:\s*[:\(]|$)'),
            'namespace': re.compile(r'^namespace\s+(\w+)'),
            'section': re.compile(r'^section(?:\s+(\w+))?'),
            'variable': re.compile(r'^variable(?:s)?\s*[:\(]'),
            'universe': re.compile(r'^universe\s+(\w+)'),
            'open': re.compile(r'^open\s+([\w\.]+)'),
            'import': re.compile(r'^import\s+([\w\.]+)'),
        }
        
        # Attribute pattern
        self.attribute_pattern = re.compile(r'^@\[([^\]]+)\]')
        
        # Docstring pattern  
        self.docstring_pattern = re.compile(r'^/--([^-]|(?:-(?!/))|(?:\n))*?-/')
        
        # Visibility patterns
        self.visibility_pattern = re.compile(r'^(private|protected)\s+')
        
        # Noncomputable pattern
        self.noncomputable_pattern = re.compile(r'^noncomputable\s+')
    
    def parse_file_enhanced(self, file_path: Path) -> Dict[str, List[LeanDeclaration]]:
        """Parse a Lean file and extract all language constructs.
        
        Returns:
            Dictionary mapping construct types to lists of declarations
        """
        try:
            content = file_path.read_text(encoding='utf-8')
            return self.parse_content_enhanced(content)
        except Exception as e:
            self.logger.error(f"Failed to parse file {file_path}: {e}")
            return {}
    
    def parse_content_enhanced(self, content: str) -> Dict[str, List[LeanDeclaration]]:
        """Parse Lean content and extract all language constructs."""
        lines = content.splitlines()
        declarations: Dict[str, List[LeanDeclaration]] = {
            construct.value: [] for construct in LeanConstruct
        }
        
        # Reset parser state
        self.current_namespace = None
        self.namespace_stack = []
        self.open_namespaces.clear()
        
        i = 0
        while i < len(lines):
            line = lines[i].strip()
            
            # Skip empty lines and comments
            if not line or line.startswith('--'):
                i += 1
                continue
            
            # Parse docstring if present
            docstring = None
            if line.startswith('/--'):
                docstring, doc_end = self._extract_docstring(lines, i)
                i = doc_end
                if i >= len(lines):
                    break
                line = lines[i].strip()
            
            # Parse attributes if present
            attributes: List[LeanAttribute] = []
            if line.startswith('@['):
                attributes, attr_end = self._extract_attributes(lines, i)
                i = attr_end
                if i >= len(lines):
                    break
                line = lines[i].strip()
            
            # Parse visibility modifier
            visibility = "public"
            visibility_match = self.visibility_pattern.match(line)
            if visibility_match:
                visibility = visibility_match.group(1)
                line = self.visibility_pattern.sub('', line).strip()
            
            # Parse noncomputable modifier
            is_noncomputable = False
            if self.noncomputable_pattern.match(line):
                is_noncomputable = True
                line = self.noncomputable_pattern.sub('', line).strip()
            
            # Try to parse as different constructs
            declaration = None
            next_line = i
            
            for construct_name, pattern in self.patterns.items():
                match = pattern.match(line)
                if match:
                    declaration, next_line = self._parse_construct(
                        construct_name, match, lines, i, 
                        docstring, attributes, visibility, is_noncomputable
                    )
                    break
            
            if declaration:
                declarations[declaration.construct_type.value].append(declaration)
                i = next_line
            else:
                i += 1
        
        return declarations
    
    def _parse_construct(self, construct_name: str, match: re.Match[str], 
                        lines: List[str], start_line: int,
                        docstring: Optional[str], attributes: List[LeanAttribute],
                        visibility: str, is_noncomputable: bool) -> tuple[Optional[LeanDeclaration], int]:
        """Parse a specific construct based on its type."""
        
        if construct_name in ['theorem', 'lemma']:
            return self._parse_theorem(match, lines, start_line, docstring, attributes, visibility)
        elif construct_name == 'definition':
            return self._parse_definition(match, lines, start_line, docstring, attributes, visibility, is_noncomputable)
        elif construct_name == 'inductive':
            return self._parse_inductive(match, lines, start_line, docstring, attributes, visibility)
        elif construct_name == 'structure':
            return self._parse_structure(match, lines, start_line, docstring, attributes, visibility)
        elif construct_name == 'class':
            return self._parse_class(match, lines, start_line, docstring, attributes, visibility)
        elif construct_name == 'instance':
            return self._parse_instance(match, lines, start_line, docstring, attributes, visibility)
        elif construct_name == 'axiom':
            return self._parse_axiom(match, lines, start_line, docstring, attributes, visibility)
        elif construct_name == 'namespace':
            return self._parse_namespace(match, lines, start_line, docstring, attributes, visibility)
        else:
            # For other constructs, create a basic declaration
            name = match.group(1) if match.groups() else f"unnamed_{start_line}"
            return LeanDeclaration(
                construct_type=LeanConstruct(construct_name),
                name=name,
                line_number=start_line + 1,
                raw_text=lines[start_line],
                namespace=self.current_namespace,
                attributes=attributes,
                docstring=docstring,
                visibility=visibility
            ), start_line + 1
    
    def _parse_theorem(self, match: re.Match[str], lines: List[str], start_line: int,
                      docstring: Optional[str], attributes: List[LeanAttribute], 
                      visibility: str) -> tuple[LeanTheorem, int]:
        """Parse theorem or lemma declaration."""
        construct_type = LeanConstruct.THEOREM if match.group(1) == 'theorem' else LeanConstruct.LEMMA
        name = match.group(2)
        
        # Extract full statement and proof
        statement, proof, end_line = self._extract_theorem_content(lines, start_line)
        
        # Extract parameters from statement
        parameters = self._extract_parameters(statement)
        
        # Extract tactics from proof
        tactics = self._extract_tactics(proof) if proof else []
        
        theorem = LeanTheorem(
            construct_type=construct_type,
            name=name,
            line_number=start_line + 1,
            raw_text='\n'.join(lines[start_line:end_line+1]),
            namespace=self.current_namespace,
            attributes=attributes,
            docstring=docstring,
            visibility=visibility,
            statement=statement,
            proof=proof,
            parameters=parameters,
            tactics=tactics
        )
        
        return theorem, end_line + 1
    
    def _parse_definition(self, match: re.Match[str], lines: List[str], start_line: int,
                         docstring: Optional[str], attributes: List[LeanAttribute],
                         visibility: str, is_noncomputable: bool) -> tuple[LeanDefinition, int]:
        """Parse definition declaration."""
        name = match.group(1)
        
        # Extract type signature and body
        type_sig, body, end_line = self._extract_definition_content(lines, start_line)
        
        # Extract parameters
        parameters = self._extract_parameters(type_sig)
        
        definition = LeanDefinition(
            construct_type=LeanConstruct.DEFINITION,
            name=name,
            line_number=start_line + 1,
            raw_text='\n'.join(lines[start_line:end_line+1]),
            namespace=self.current_namespace,
            attributes=attributes,
            docstring=docstring,
            visibility=visibility,
            type_signature=type_sig,
            parameters=parameters,
            body=body,
            is_noncomputable=is_noncomputable
        )
        
        return definition, end_line + 1
    
    def _parse_inductive(self, match: re.Match[str], lines: List[str], start_line: int,
                        docstring: Optional[str], attributes: List[LeanAttribute],
                        visibility: str) -> tuple[LeanInductive, int]:
        """Parse inductive type declaration."""
        name = match.group(1)
        
        # Extract type signature and constructors
        type_sig, constructors, derives, end_line = self._extract_inductive_content(lines, start_line)
        
        # Extract parameters
        parameters = self._extract_parameters(type_sig)
        
        inductive = LeanInductive(
            construct_type=LeanConstruct.INDUCTIVE,
            name=name,
            line_number=start_line + 1,
            raw_text='\n'.join(lines[start_line:end_line+1]),
            namespace=self.current_namespace,
            attributes=attributes,
            docstring=docstring,
            visibility=visibility,
            type_signature=type_sig,
            parameters=parameters,
            constructors=constructors,
            derives=derives
        )
        
        return inductive, end_line + 1
    
    def _parse_structure(self, match: re.Match[str], lines: List[str], start_line: int,
                        docstring: Optional[str], attributes: List[LeanAttribute],
                        visibility: str) -> tuple[LeanStructure, int]:
        """Parse structure declaration."""
        name = match.group(1)
        
        # Extract parameters, extends, and fields
        parameters, extends, fields, derives, end_line = self._extract_structure_content(lines, start_line)
        
        structure = LeanStructure(
            construct_type=LeanConstruct.STRUCTURE,
            name=name,
            line_number=start_line + 1,
            raw_text='\n'.join(lines[start_line:end_line+1]),
            namespace=self.current_namespace,
            attributes=attributes,
            docstring=docstring,
            visibility=visibility,
            parameters=parameters,
            extends=extends,
            fields=fields,
            derives=derives
        )
        
        return structure, end_line + 1
    
    def _parse_class(self, match: re.Match[str], lines: List[str], start_line: int,
                    docstring: Optional[str], attributes: List[LeanAttribute],
                    visibility: str) -> tuple[LeanClass, int]:
        """Parse class declaration."""
        name = match.group(1)
        
        # Extract parameters, extends, and fields (similar to structure)
        parameters, extends, fields, _, end_line = self._extract_structure_content(lines, start_line)
        
        class_decl = LeanClass(
            construct_type=LeanConstruct.CLASS,
            name=name,
            line_number=start_line + 1,
            raw_text='\n'.join(lines[start_line:end_line+1]),
            namespace=self.current_namespace,
            attributes=attributes,
            docstring=docstring,
            visibility=visibility,
            parameters=parameters,
            extends=extends,
            fields=fields
        )
        
        return class_decl, end_line + 1
    
    def _parse_instance(self, match: re.Match[str], lines: List[str], start_line: int,
                       docstring: Optional[str], attributes: List[LeanAttribute],
                       visibility: str) -> tuple[LeanInstance, int]:
        """Parse instance declaration."""
        name = match.group(1) if match.group(1) else f"instance_{start_line}"
        
        # Extract class name, type, and proof
        class_name, instance_type, parameters, proof, end_line = self._extract_instance_content(lines, start_line)
        
        instance = LeanInstance(
            construct_type=LeanConstruct.INSTANCE,
            name=name,
            line_number=start_line + 1,
            raw_text='\n'.join(lines[start_line:end_line+1]),
            namespace=self.current_namespace,
            attributes=attributes,
            docstring=docstring,
            visibility=visibility,
            class_name=class_name,
            instance_type=instance_type,
            parameters=parameters,
            proof=proof
        )
        
        return instance, end_line + 1
    
    def _parse_axiom(self, match: re.Match[str], lines: List[str], start_line: int,
                    docstring: Optional[str], attributes: List[LeanAttribute],
                    visibility: str) -> tuple[LeanTheorem, int]:
        """Parse axiom declaration (treated as theorem without proof)."""
        name = match.group(1)
        
        # Extract statement (axioms don't have proofs)
        statement, _, end_line = self._extract_theorem_content(lines, start_line, expect_proof=False)
        
        axiom = LeanTheorem(
            construct_type=LeanConstruct.AXIOM,
            name=name,
            line_number=start_line + 1,
            raw_text='\n'.join(lines[start_line:end_line+1]),
            namespace=self.current_namespace,
            attributes=attributes,
            docstring=docstring,
            visibility=visibility,
            statement=statement,
            proof=None
        )
        
        return axiom, end_line + 1
    
    def _parse_namespace(self, match: re.Match[str], lines: List[str], start_line: int,
                        docstring: Optional[str], attributes: List[LeanAttribute],
                        visibility: str) -> tuple[LeanNamespace, int]:
        """Parse namespace declaration."""
        name = match.group(1)
        
        # Update namespace context
        if self.current_namespace:
            self.namespace_stack.append(self.current_namespace)
            self.current_namespace = f"{self.current_namespace}.{name}"
        else:
            self.current_namespace = name
        
        namespace = LeanNamespace(
            construct_type=LeanConstruct.NAMESPACE,
            name=name,
            line_number=start_line + 1,
            raw_text=lines[start_line],
            namespace=self.current_namespace,
            attributes=attributes,
            docstring=docstring,
            visibility=visibility
        )
        
        return namespace, start_line + 1
    
    # Helper methods for content extraction
    
    def _extract_docstring(self, lines: List[str], start_line: int) -> tuple[Optional[str], int]:
        """Extract docstring starting from given line."""
        if not lines[start_line].strip().startswith('/--'):
            return None, start_line
        
        docstring_lines = []
        i = start_line
        
        while i < len(lines):
            line = lines[i]
            docstring_lines.append(line)
            if '-/' in line:
                break
            i += 1
        
        docstring = '\n'.join(docstring_lines)
        # Clean up docstring format
        docstring = re.sub(r'/--\s*', '', docstring)
        docstring = re.sub(r'\s*-/', '', docstring)
        
        return docstring.strip(), i + 1
    
    def _extract_attributes(self, lines: List[str], start_line: int) -> tuple[List[LeanAttribute], int]:
        """Extract attributes starting from given line."""
        attributes = []
        i = start_line
        
        while i < len(lines) and lines[i].strip().startswith('@['):
            line = lines[i].strip()
            match = self.attribute_pattern.match(line)
            if match:
                attr_content = match.group(1)
                # Parse multiple attributes separated by commas
                attr_names = [attr.strip() for attr in attr_content.split(',')]
                for attr_name in attr_names:
                    try:
                        attributes.append(LeanAttribute(attr_name))
                    except ValueError:
                        # Unknown attribute, skip
                        pass
            i += 1
        
        return attributes, i
    
    def _extract_theorem_content(self, lines: List[str], start_line: int, 
                                expect_proof: bool = True) -> tuple[str, Optional[str], int]:
        """Extract theorem statement and proof."""
        # This is a simplified implementation
        # In a full implementation, this would need to handle complex parsing
        
        i = start_line
        statement_parts = []
        proof_parts = []
        in_proof = False
        
        while i < len(lines):
            line = lines[i].strip()
            
            if ':=' in line and not in_proof:
                # Start of proof
                statement_parts.append(line.split(':=')[0].strip())
                if expect_proof:
                    proof_start = line.split(':=')[1].strip()
                    if proof_start:
                        proof_parts.append(proof_start)
                    in_proof = True
                break
            elif not in_proof:
                statement_parts.append(line)
            else:
                proof_parts.append(line)
            
            i += 1
        
        # Continue extracting proof if we started
        if in_proof and expect_proof:
            i += 1
            brace_count = 0
            
            while i < len(lines):
                line = lines[i].strip()
                proof_parts.append(line)
                
                # Simple brace matching (would need more sophisticated parsing)
                brace_count += line.count('{') - line.count('}')
                
                # Check for proof end indicators
                if (brace_count == 0 and 
                    (line.endswith('qed') or line.endswith('sorry') or 
                     any(keyword in line for keyword in ['theorem ', 'lemma ', 'def ', 'end ']))):
                    break
                
                i += 1
        
        statement = ' '.join(statement_parts).strip()
        proof = ' '.join(proof_parts).strip() if proof_parts else None
        
        return statement, proof, i
    
    def _extract_definition_content(self, lines: List[str], start_line: int) -> tuple[str, Optional[str], int]:
        """Extract definition type signature and body."""
        # Simplified implementation
        return self._extract_theorem_content(lines, start_line, expect_proof=True)
    
    def _extract_inductive_content(self, lines: List[str], start_line: int) -> tuple[str, List[Dict[str, str]], List[str], int]:
        """Extract inductive type content."""
        # Simplified implementation - would need complex parsing for full support
        type_sig = ""
        constructors = []
        derives = []
        
        i = start_line
        while i < len(lines) and not lines[i].strip().startswith('end'):
            line = lines[i].strip()
            if line.startswith('|'):
                # Constructor
                constructor_name = line.split(':')[0].replace('|', '').strip()
                constructor_type = line.split(':')[1].strip() if ':' in line else ""
                constructors.append({"name": constructor_name, "type": constructor_type})
            elif 'deriving' in line:
                # Derives clause
                derives_part = line.split('deriving')[1].strip()
                derives = [d.strip() for d in derives_part.split(',')]
            elif i == start_line:
                # Type signature
                type_sig = line
            i += 1
        
        return type_sig, constructors, derives, i
    
    def _extract_structure_content(self, lines: List[str], start_line: int) -> tuple[List[str], List[str], List[Dict[str, str]], List[str], int]:
        """Extract structure content."""
        # Simplified implementation
        parameters: List[str] = []
        extends = []
        fields = []
        derives = []
        
        i = start_line
        while i < len(lines) and not any(keyword in lines[i] for keyword in ['end', 'theorem', 'lemma', 'def']):
            line = lines[i].strip()
            if 'extends' in line:
                extends_part = line.split('extends')[1].split('where')[0].strip()
                extends = [e.strip() for e in extends_part.split(',')]
            elif line and not line.startswith('where') and ':' in line:
                # Field
                field_name = line.split(':')[0].strip()
                field_type = line.split(':')[1].strip()
                fields.append({"name": field_name, "type": field_type})
            elif 'deriving' in line:
                derives_part = line.split('deriving')[1].strip()
                derives = [d.strip() for d in derives_part.split(',')]
            i += 1
        
        return parameters, extends, fields, derives, i
    
    def _extract_instance_content(self, lines: List[str], start_line: int) -> tuple[str, str, List[str], Optional[str], int]:
        """Extract instance content."""
        # Simplified implementation
        class_name = ""
        instance_type = ""
        parameters: List[str] = []
        proof = None
        
        i = start_line
        line = lines[i].strip()
        
        # Parse instance line
        if ':' in line:
            parts = line.split(':')
            if len(parts) >= 2:
                instance_type = parts[1].strip()
                class_name = instance_type.split()[0] if instance_type else ""
        
        # Extract proof if present
        _, proof, end_line = self._extract_theorem_content(lines, start_line, expect_proof=True)
        
        return class_name, instance_type, parameters, proof, end_line
    
    def _extract_parameters(self, content: str) -> List[str]:
        """Extract parameters from a declaration."""
        # Simplified parameter extraction
        parameters = []
        
        # Look for parameter patterns like (x : Type) or {α : Type*}
        param_patterns = [
            re.findall(r'\(([^:]+):[^)]+\)', content),
            re.findall(r'\{([^:]+):[^}]+\}', content),
            re.findall(r'\[([^:]+):[^\]]+\]', content),
        ]
        
        for pattern_matches in param_patterns:
            for match in pattern_matches:
                param_names = [p.strip() for p in match.split(',')]
                parameters.extend(param_names)
        
        return parameters
    
    def _extract_tactics(self, proof: str) -> List[str]:
        """Extract tactics used in proof."""
        if not proof:
            return []
        
        # Common Lean tactics
        common_tactics = [
            'simp', 'rw', 'rewrite', 'exact', 'apply', 'intro', 'intros',
            'cases', 'induction', 'constructor', 'left', 'right', 'split',
            'have', 'show', 'suffices', 'by_contra', 'by_contradiction',
            'reflexivity', 'symmetry', 'transitivity', 'assumption',
            'sorry', 'admit', 'ring', 'abel', 'linarith', 'omega',
            'norm_num', 'norm_cast', 'push_neg', 'contrapose'
        ]
        
        tactics_found = []
        for tactic in common_tactics:
            if re.search(rf'\b{tactic}\b', proof):
                tactics_found.append(tactic)
        
        return tactics_found
    
    def get_theorems_for_proof_sketcher(self, declarations: Dict[str, List[LeanDeclaration]]) -> List[TheoremInfo]:
        """Convert enhanced parsing results to TheoremInfo for compatibility."""
        theorem_infos = []
        
        # Convert theorems and lemmas
        for theorem in declarations.get('theorem', []) + declarations.get('lemma', []):
            if isinstance(theorem, LeanTheorem):
                theorem_infos.append(theorem.to_theorem_info())
        
        # Convert axioms
        for axiom in declarations.get('axiom', []):
            if isinstance(axiom, LeanTheorem):
                theorem_infos.append(axiom.to_theorem_info())
        
        return theorem_infos