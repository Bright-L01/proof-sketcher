# Proof Sketcher Architecture Overview

## 🏗️ System Architecture

Proof Sketcher follows a modular, plugin-based architecture designed for extensibility, maintainability, and performance. The system transforms Lean 4 mathematical proofs into natural language explanations through a sophisticated pipeline.

```
┌─────────────────────────────────────────────────────────────────┐
│                         Proof Sketcher                         │
├─────────────────────────────────────────────────────────────────┤
│  CLI Layer                                                      │
│  ┌─────────────┬─────────────┬─────────────┬─────────────────┐  │
│  │   Commands  │   Config    │   Cache     │   Batch         │  │
│  │   Management│   Management│   Management│   Processing    │  │
│  └─────────────┴─────────────┴─────────────┴─────────────────┘  │
├─────────────────────────────────────────────────────────────────┤
│  Core Processing Pipeline                                       │
│  ┌─────────────┬─────────────┬─────────────┬─────────────────┐  │
│  │   Parser    │  Generator  │  Animator   │   Exporter      │  │
│  │   Layer     │   Layer     │   Layer     │   Layer         │  │
│  └─────────────┴─────────────┴─────────────┴─────────────────┘  │
├─────────────────────────────────────────────────────────────────┤
│  Infrastructure & Cross-Cutting Concerns                       │
│  ┌─────────────┬─────────────┬─────────────┬─────────────────┐  │
│  │   Error     │  Resource   │  Security   │   Monitoring    │  │
│  │   Handling  │  Management │  Framework  │   & Logging     │  │
│  └─────────────┴─────────────┴─────────────┴─────────────────┘  │
└─────────────────────────────────────────────────────────────────┘
```

## 🧩 Core Components

### 1. Parser Layer (`src/proof_sketcher/parser/`)

**Responsibility**: Extract structured information from Lean 4 files

**Key Components**:
- `LeanParser`: Main parsing engine
- `EnhancedParser`: Extended language support (inductive types, structures, classes)
- `TheoremInfo`: Structured representation of theorems
- `ParseResult`: Comprehensive parsing results with error handling

**Architecture**:
```python
# Core parsing interface
class LeanParser:
    def parse_file(self, file_path: Path) -> ParseResult:
        """Parse a Lean file and extract theorem information."""
        pass
    
    def parse_theorem(self, theorem_text: str) -> Optional[TheoremInfo]:
        """Parse a single theorem from text."""
        pass
```

**Key Features**:
- Robust error handling with detailed error messages
- Support for complex Lean 4 constructs
- Dependency tracking and import resolution
- Line number and location tracking

### 2. Generator Layer (`src/proof_sketcher/generator/`)

**Responsibility**: Transform parsed theorems into natural language explanations

**Key Components**:
- `AIGenerator`: Claude-powered explanation generation
- `OfflineGenerator`: AST-based explanations without AI
- `PromptTemplates`: Modular prompt system
- `CacheManager`: Intelligent response caching

**Architecture**:
```python
# Generation pipeline
class AIGenerator:
    def generate_proof_sketch(self, theorem: TheoremInfo) -> ProofSketch:
        """Generate comprehensive explanation for a theorem."""
        pass
    
    def generate_with_context(self, theorem: TheoremInfo, 
                            context: MathematicalContext) -> ProofSketch:
        """Generate explanation with mathematical context."""
        pass
```

**Generation Types**:
- **Proof Sketch**: Comprehensive mathematical explanation
- **ELI5**: Intuitive, analogy-rich explanations
- **Tactic Explanation**: Lean 4 tactic breakdowns
- **Step-by-Step**: Detailed proof walkthroughs
- **Mathematical Context**: Historical and theoretical background

### 3. Animator Layer (`src/proof_sketcher/animator/`)

**Responsibility**: Create mathematical visualizations and animations

**Key Components**:
- `ManimMCPClient`: Integration with Manim MCP server
- `SceneBuilder`: Animation scene construction
- `FormulaExtractor`: Mathematical formula parsing
- `MockMCPServer`: Testing and fallback animations

**Architecture**:
```python
# Animation pipeline
class ManimMCPClient:
    async def render_animation(self, request: AnimationRequest) -> AnimationResponse:
        """Render mathematical animation from proof steps."""
        pass
    
    def create_fallback_animation(self, theorem: str) -> Path:
        """Generate static visualization when Manim unavailable."""
        pass
```

**Features**:
- Circuit breaker pattern for reliability
- Exponential backoff retry logic
- Fallback to static images
- Resource monitoring and timeout handling

### 4. Exporter Layer (`src/proof_sketcher/exporter/`)

**Responsibility**: Generate multiple output formats from explanations

**Key Components**:
- `HTMLExporter`: Interactive web documentation
- `MarkdownExporter`: GitHub-compatible documentation
- `PDFExporter`: Print-ready academic format
- `JupyterExporter`: Interactive notebooks

**Architecture**:
```python
# Export pipeline
class HTMLExporter:
    def export_multiple(self, sketches: List[ProofSketch], 
                       context: ExportContext) -> ExportResult:
        """Export multiple theorem explanations to HTML."""
        pass
    
    def export_with_animations(self, sketch: ProofSketch, 
                             animations: Dict[str, Path]) -> ExportResult:
        """Export with embedded animations."""
        pass
```

**Output Features**:
- Responsive design with doc-gen4 compatibility
- Embedded animations with fallback support
- Cross-references and navigation
- Theme support and customization

## 🔄 Processing Pipeline

### Standard Processing Flow

1. **Input Validation**
   - File existence and format validation
   - Lean syntax verification
   - Dependency resolution

2. **Parsing Phase**
   ```
   Lean File → LeanParser → TheoremInfo[] → ParseResult
   ```

3. **Generation Phase**
   ```
   TheoremInfo → PromptTemplate → AIGenerator → ProofSketch
   ```

4. **Animation Phase** (Optional)
   ```
   ProofSketch → SceneBuilder → ManimMCP → Animation
   ```

5. **Export Phase**
   ```
   ProofSketch + Animation → Exporter → Output Files
   ```

### Batch Processing Flow

```
Directory → FileDiscovery → BatchJob[] → ParallelExecution → BatchResult
```

**Features**:
- Parallel execution with configurable workers
- Memory monitoring and resource limits
- Error isolation and recovery
- Progress tracking and reporting

## 🛡️ Cross-Cutting Concerns

### Error Handling (`src/proof_sketcher/core/errors.py`)

**Philosophy**: Comprehensive error hierarchy with recovery strategies

```python
# Error hierarchy
ProofSketcherError
├── ParserError
│   ├── LeanSyntaxError
│   ├── LeanTimeoutError
│   └── LeanExecutableError
├── GeneratorError
│   ├── AIServiceError
│   ├── PromptError
│   └── AITimeoutError
├── AnimatorError
│   ├── MCPConnectionError
│   ├── AnimationTimeoutError
│   └── AnimationRenderError
└── ExporterError
    ├── ExportFormatError
    ├── TemplateError
    └── AssetError
```

**Features**:
- Detailed error context with recovery suggestions
- Error code classification for programmatic handling
- Graceful degradation strategies
- User-friendly error messages

### Resource Management (`src/proof_sketcher/core/resources.py`)

**Components**:
- `TempFileManager`: Automatic cleanup of temporary files
- `ProcessManager`: Subprocess lifecycle management
- `ResourceMonitor`: Memory and disk usage monitoring
- `ResourceLimits`: Configurable resource constraints

**Features**:
- Automatic resource cleanup on exit
- Memory usage monitoring with configurable limits
- Process timeout handling
- Disk space management

### Security Framework

**Components**:
- Static security analysis with Bandit
- Dependency vulnerability scanning with Safety
- Input validation and sanitization
- Secure file handling

**Practices**:
- No hardcoded secrets or credentials
- Comprehensive input validation
- Secure temporary file handling
- Regular dependency updates

### Configuration Management (`src/proof_sketcher/config/`)

**Architecture**:
```python
# Hierarchical configuration
ProofSketcherConfig
├── ParserConfig
├── GeneratorConfig
├── AnimatorConfig
├── ExporterConfig
└── CacheConfig
```

**Sources** (in priority order):
1. Command-line arguments
2. Environment variables
3. Configuration files (YAML)
4. Default values

## 🔌 Plugin Architecture

### Extension Points

1. **Parser Extensions**: Support for new Lean constructs
2. **Generator Extensions**: Custom explanation types
3. **Exporter Extensions**: New output formats
4. **Animation Extensions**: Custom visualization styles

### Plugin Interface

```python
class ProofSketcherPlugin:
    def register_parsers(self) -> List[ParserExtension]:
        """Register custom parser extensions."""
        pass
    
    def register_generators(self) -> List[GeneratorExtension]:
        """Register custom explanation generators."""
        pass
    
    def register_exporters(self) -> List[ExporterExtension]:
        """Register custom export formats."""
        pass
```

## 📊 Performance Characteristics

### Benchmarks (Reference System)

- **Parsing**: ~50 theorems/second
- **Generation**: ~1.1 theorems/second (AI-dependent)
- **Animation**: ~0.3 animations/second (complexity-dependent)
- **Export**: ~100 documents/second

### Scalability

- **Horizontal**: Parallel batch processing
- **Vertical**: Resource monitoring and limits
- **Caching**: Intelligent response caching (95%+ hit rate)
- **Memory**: Configurable limits and monitoring

## 🔧 Development Workflow

### Code Quality

- **Type Safety**: 100% type coverage with MyPy
- **Test Coverage**: 95%+ with comprehensive test suites
- **Code Style**: Black formatting, Ruff linting
- **Security**: Bandit scanning, dependency monitoring

### CI/CD Pipeline

```
Code → Security Scan → Type Check → Test → Build → Deploy
     ↓               ↓             ↓      ↓       ↓
   Bandit         MyPy        pytest  Package  Release
   Safety                              Check
   Semgrep
```

## 🚀 Future Architecture

### Planned Enhancements

1. **Microservices**: Separate parsing, generation, and animation services
2. **Event-Driven**: Async processing with message queues
3. **Distributed**: Multi-node processing for large projects
4. **Real-Time**: WebSocket-based live preview
5. **Cloud-Native**: Kubernetes deployment and scaling

### Extension Roadmap

1. **Language Support**: Coq, Agda, Isabelle parsers
2. **AI Models**: Multi-model support (GPT, Gemini, etc.)
3. **Visualization**: 3D animations, interactive diagrams
4. **Integration**: VSCode extension, web interface
5. **Collaboration**: Multi-user editing and reviewing

---

*This architecture enables Proof Sketcher to handle everything from simple tutorial theorems to complex research-level mathematics while maintaining reliability, performance, and extensibility.*