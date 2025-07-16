"""Template engine for rendering educational content in doc-gen4 HTML."""

from pathlib import Path
from typing import Any, Dict

from jinja2 import Environment, FileSystemLoader

# from ..exporter.html import HTMLExporter


class EducationalTemplateEngine:
    """Renders educational content into HTML templates compatible with doc-gen4."""

    def __init__(self):
        """Initialize the template engine."""
        # Get template directory
        template_dir = Path(__file__).parent / "templates"
        template_dir.mkdir(exist_ok=True)

        # Initialize Jinja2 environment
        self.env = Environment(loader=FileSystemLoader(template_dir), autoescape=True)

        # Create default templates if they don't exist
        self._create_default_templates()

    def render_educational_declaration(
        self,
        declaration: Dict[str, Any],
        template_name: str = "educational_declaration.html",
    ) -> str:
        """Render an educational declaration to HTML.

        Args:
            declaration: Declaration data with educational content
            template_name: Name of the template to use

        Returns:
            Rendered HTML string
        """
        template = self.env.get_template(template_name)
        return template.render(declaration=declaration)

    def render_educational_module(
        self,
        module_data: Dict[str, Any],
        template_name: str = "educational_module.html",
    ) -> str:
        """Render an educational module to HTML.

        Args:
            module_data: Module data with educational content
            template_name: Name of the template to use

        Returns:
            Rendered HTML string
        """
        template = self.env.get_template(template_name)
        return template.render(module=module_data)

    def render_progressive_explanation(
        self,
        explanation_data: Dict[str, Any],
        template_name: str = "progressive_explanation.html",
    ) -> str:
        """Render progressive explanation to HTML.

        Args:
            explanation_data: Progressive explanation data
            template_name: Name of the template to use

        Returns:
            Rendered HTML string
        """
        template = self.env.get_template(template_name)
        return template.render(explanation=explanation_data)

    def create_educational_assets(self, output_dir: Path) -> None:
        """Create CSS and JavaScript assets for educational content.

        Args:
            output_dir: Directory to write assets
        """
        assets_dir = output_dir / "assets"
        assets_dir.mkdir(parents=True, exist_ok=True)

        # Create CSS
        css_content = self._create_educational_css()
        with open(assets_dir / "educational.css", "w") as f:
            f.write(css_content)

        # Create JavaScript
        js_content = self._create_educational_js()
        with open(assets_dir / "educational.js", "w") as f:
            f.write(js_content)

    def _create_default_templates(self) -> None:
        """Create default templates if they don't exist."""
        template_dir = Path(__file__).parent / "templates"

        # Educational declaration template
        decl_template = template_dir / "educational_declaration.html"
        if not decl_template.exists():
            decl_template.write_text(self._get_declaration_template())

        # Progressive explanation template
        prog_template = template_dir / "progressive_explanation.html"
        if not prog_template.exists():
            prog_template.write_text(self._get_progressive_template())

        # Educational module template
        mod_template = template_dir / "educational_module.html"
        if not mod_template.exists():
            mod_template.write_text(self._get_module_template())

    def _get_declaration_template(self) -> str:
        """Get the educational declaration template."""
        return """
<div class="educational-declaration" data-name="{{ declaration.name }}">
    <div class="declaration-header">
        <h3 class="declaration-name">{{ declaration.name }}</h3>
        <span class="declaration-kind">{{ declaration.kind }}</span>
    </div>

    <div class="declaration-statement">
        <code class="lean-code">{{ declaration.type }}</code>
    </div>

    {% if declaration.doc %}
    <div class="declaration-doc">
        <p>{{ declaration.doc }}</p>
    </div>
    {% endif %}

    {% if declaration.educational_content %}
    <div class="educational-content">
        <div class="explanation-tabs">
            <button class="tab-button active" data-level="beginner">
                <span class="tab-icon">🌱</span>
                Beginner
            </button>
            <button class="tab-button" data-level="intermediate">
                <span class="tab-icon">🌿</span>
                Intermediate
            </button>
            <button class="tab-button" data-level="advanced">
                <span class="tab-icon">🌳</span>
                Advanced
            </button>
        </div>

        <div class="explanation-content" id="beginner-content">
            <div class="progressive-explanation">
                <div class="explanation-overview">
                    <h4>{{ declaration.educational_content.progressive_explanations.beginner.title }}</h4>
                    <p>{{ declaration.educational_content.progressive_explanations.beginner.overview }}</p>
                </div>
                {% if declaration.educational_content.progressive_explanations.beginner.intuition %}
                <div class="explanation-intuition">
                    <h5>Intuition</h5>
                    <p>{{ declaration.educational_content.progressive_explanations.beginner.intuition }}</p>
                </div>
                {% endif %}
            </div>
        </div>

        <div class="explanation-content" id="intermediate-content" style="display: none;">
            <div class="progressive-explanation">
                <div class="explanation-overview">
                    <h4>{{ declaration.educational_content.progressive_explanations.intermediate.title }}</h4>
                    <p>{{ declaration.educational_content.progressive_explanations.intermediate.overview }}</p>
                </div>
            </div>
        </div>

        <div class="explanation-content" id="advanced-content" style="display: none;">
            <div class="progressive-explanation">
                <div class="explanation-overview">
                    <h4>{{ declaration.educational_content.progressive_explanations.advanced.title }}</h4>
                    <p>{{ declaration.educational_content.progressive_explanations.advanced.overview }}</p>
                </div>
            </div>
        </div>

        {% if declaration.educational_content.key_concepts %}
        <div class="key-concepts">
            <h4>Key Concepts</h4>
            <div class="concepts-grid">
                {% for concept in declaration.educational_content.key_concepts %}
                <div class="concept-card">
                    <h5>{{ concept.name }}</h5>
                    <p>{{ concept.explanation }}</p>
                </div>
                {% endfor %}
            </div>
        </div>
        {% endif %}

        {% if declaration.educational_content.learning_pathway %}
        <div class="learning-pathway">
            <h4>Learning Pathway</h4>
            <ol class="pathway-steps">
                {% for step in declaration.educational_content.learning_pathway %}
                <li class="pathway-step">
                    <h5>{{ step.title }}</h5>
                    <p>{{ step.explanation }}</p>
                </li>
                {% endfor %}
            </ol>
        </div>
        {% endif %}

        {% if declaration.educational_content.interactive_elements %}
        <div class="interactive-elements">
            {% for element in declaration.educational_content.interactive_elements %}
            <div class="interactive-element" data-type="{{ element.type }}">
                <h5>{{ element.title }}</h5>
                <div class="element-content">{{ element.content }}</div>
            </div>
            {% endfor %}
        </div>
        {% endif %}
    </div>
    {% endif %}
</div>
        """

    def _get_progressive_template(self) -> str:
        """Get the progressive explanation template."""
        return """
<div class="progressive-explanation">
    <div class="explanation-overview">
        <h4>{{ explanation.title }}</h4>
        <p>{{ explanation.overview }}</p>
    </div>

    {% if explanation.intuition %}
    <div class="explanation-intuition">
        <h5>Intuition</h5>
        <p>{{ explanation.intuition }}</p>
    </div>
    {% endif %}

    {% if explanation.main_ideas %}
    <div class="explanation-main-ideas">
        <h5>Main Ideas</h5>
        <ul>
            {% for idea in explanation.main_ideas %}
            <li>{{ idea }}</li>
            {% endfor %}
        </ul>
    </div>
    {% endif %}

    {% if explanation.examples %}
    <div class="explanation-examples">
        <h5>Examples</h5>
        {% for example in explanation.examples %}
        <div class="example-item">
            <strong>{{ example.title }}</strong>
            <p>{{ example.content }}</p>
        </div>
        {% endfor %}
    </div>
    {% endif %}

    {% if explanation.connections %}
    <div class="explanation-connections">
        <h5>Connections</h5>
        <ul>
            {% for connection in explanation.connections %}
            <li>{{ connection }}</li>
            {% endfor %}
        </ul>
    </div>
    {% endif %}
</div>
        """

    def _get_module_template(self) -> str:
        """Get the educational module template."""
        return """
<div class="educational-module">
    <div class="module-header">
        <h2>{{ module.name }}</h2>
        {% if module.doc %}
        <p class="module-doc">{{ module.doc }}</p>
        {% endif %}
    </div>

    {% if module.educational_metadata %}
    <div class="module-stats">
        <div class="stat-item">
            <span class="stat-label">Total Declarations:</span>
            <span class="stat-value">{{ module.educational_metadata.total_declarations }}</span>
        </div>
        <div class="stat-item">
            <span class="stat-label">Educational Content:</span>
            <span class="stat-value">{{ module.educational_metadata.educational_declarations }}</span>
        </div>
        <div class="stat-item">
            <span class="stat-label">Generated:</span>
            <span class="stat-value">{{ module.educational_metadata.generated_at }}</span>
        </div>
    </div>
    {% endif %}

    <div class="module-declarations">
        {% for declaration in module.declarations %}
        <div class="educational-declaration" data-name="{{ declaration.name }}">
            <div class="declaration-header">
                <h3 class="declaration-name">{{ declaration.name }}</h3>
                <span class="declaration-kind">{{ declaration.kind }}</span>
            </div>
            <div class="declaration-statement">
                <code class="lean-code">{{ declaration.type }}</code>
            </div>
            {% if declaration.doc %}
            <div class="declaration-doc">
                <p>{{ declaration.doc }}</p>
            </div>
            {% endif %}
        </div>
        {% endfor %}
    </div>
</div>
        """

    def _create_educational_css(self) -> str:
        """Create CSS for educational content."""
        return """
/* Educational Content Styles */
.educational-declaration {
    border: 1px solid #e0e0e0;
    border-radius: 8px;
    margin: 1rem 0;
    padding: 1rem;
    background: #fafafa;
}

.declaration-header {
    display: flex;
    justify-content: space-between;
    align-items: center;
    margin-bottom: 1rem;
}

.declaration-name {
    margin: 0;
    color: #2c3e50;
    font-family: 'Fira Code', monospace;
}

.declaration-kind {
    background: #3498db;
    color: white;
    padding: 0.25rem 0.5rem;
    border-radius: 4px;
    font-size: 0.8rem;
    text-transform: uppercase;
}

.declaration-statement {
    background: #f8f9fa;
    border-left: 4px solid #3498db;
    padding: 1rem;
    margin: 1rem 0;
    border-radius: 4px;
}

.lean-code {
    font-family: 'Fira Code', monospace;
    font-size: 0.9rem;
    background: none;
    padding: 0;
}

.educational-content {
    margin-top: 1.5rem;
    border-top: 1px solid #e0e0e0;
    padding-top: 1rem;
}

.explanation-tabs {
    display: flex;
    gap: 0.5rem;
    margin-bottom: 1rem;
}

.tab-button {
    background: #ecf0f1;
    border: none;
    padding: 0.5rem 1rem;
    border-radius: 4px;
    cursor: pointer;
    display: flex;
    align-items: center;
    gap: 0.5rem;
    transition: all 0.3s ease;
}

.tab-button.active {
    background: #3498db;
    color: white;
}

.tab-button:hover {
    background: #bdc3c7;
}

.tab-button.active:hover {
    background: #2980b9;
}

.tab-icon {
    font-size: 1.2rem;
}

.explanation-content {
    background: white;
    border-radius: 4px;
    padding: 1rem;
    margin-bottom: 1rem;
}

.key-concepts {
    margin-top: 1.5rem;
}

.concepts-grid {
    display: grid;
    grid-template-columns: repeat(auto-fit, minmax(250px, 1fr));
    gap: 1rem;
    margin-top: 1rem;
}

.concept-card {
    background: #e8f4f8;
    border-radius: 4px;
    padding: 1rem;
    border-left: 4px solid #3498db;
}

.concept-card h5 {
    margin: 0 0 0.5rem 0;
    color: #2c3e50;
}

.learning-pathway {
    margin-top: 1.5rem;
}

.pathway-steps {
    margin-top: 1rem;
    padding-left: 1rem;
}

.pathway-step {
    margin-bottom: 1rem;
    padding: 0.5rem;
    background: #f8f9fa;
    border-radius: 4px;
}

.pathway-step h5 {
    margin: 0 0 0.5rem 0;
    color: #2c3e50;
}

.interactive-elements {
    margin-top: 1.5rem;
}

.interactive-element {
    background: #fff3cd;
    border: 1px solid #ffeaa7;
    border-radius: 4px;
    padding: 1rem;
    margin-bottom: 1rem;
}

.interactive-element h5 {
    margin: 0 0 0.5rem 0;
    color: #856404;
}

.element-content {
    color: #856404;
}

.module-stats {
    display: flex;
    gap: 2rem;
    margin: 1rem 0;
    padding: 1rem;
    background: #f8f9fa;
    border-radius: 4px;
}

.stat-item {
    display: flex;
    flex-direction: column;
    gap: 0.25rem;
}

.stat-label {
    font-size: 0.8rem;
    color: #6c757d;
    text-transform: uppercase;
}

.stat-value {
    font-weight: bold;
    color: #2c3e50;
}

/* Responsive design */
@media (max-width: 768px) {
    .explanation-tabs {
        flex-direction: column;
    }

    .concepts-grid {
        grid-template-columns: 1fr;
    }

    .module-stats {
        flex-direction: column;
        gap: 1rem;
    }
}
        """

    def _create_educational_js(self) -> str:
        """Create JavaScript for educational content."""
        return """
// Educational Content JavaScript
document.addEventListener('DOMContentLoaded', function() {
    // Initialize tab switching
    initializeTabs();

    // Initialize interactive elements
    initializeInteractiveElements();

    // Initialize educational features
    initializeEducationalFeatures();
});

function initializeTabs() {
    const tabButtons = document.querySelectorAll('.tab-button');

    tabButtons.forEach(button => {
        button.addEventListener('click', function() {
            const level = this.dataset.level;
            const container = this.closest('.educational-content');

            // Update active tab
            container.querySelectorAll('.tab-button').forEach(btn => {
                btn.classList.remove('active');
            });
            this.classList.add('active');

            // Show corresponding content
            container.querySelectorAll('.explanation-content').forEach(content => {
                content.style.display = 'none';
            });
            container.querySelector(`#${level}-content`).style.display = 'block';
        });
    });
}

function initializeInteractiveElements() {
    const interactiveElements = document.querySelectorAll('.interactive-element');

    interactiveElements.forEach(element => {
        const type = element.dataset.type;

        if (type === 'expandable') {
            makeExpandable(element);
        } else if (type === 'visualization') {
            addVisualizationButton(element);
        }
    });
}

function makeExpandable(element) {
    const content = element.querySelector('.element-content');
    const title = element.querySelector('h5');

    // Initially collapse content
    content.style.display = 'none';
    element.style.cursor = 'pointer';

    // Add expand/collapse indicator
    const indicator = document.createElement('span');
    indicator.textContent = ' [+]';
    indicator.style.color = '#3498db';
    title.appendChild(indicator);

    element.addEventListener('click', function() {
        if (content.style.display === 'none') {
            content.style.display = 'block';
            indicator.textContent = ' [-]';
        } else {
            content.style.display = 'none';
            indicator.textContent = ' [+]';
        }
    });
}

function addVisualizationButton(element) {
    const button = document.createElement('button');
    button.textContent = 'Show Visualization';
    button.className = 'visualization-button';
    button.style.cssText = `
        background: #3498db;
        color: white;
        border: none;
        padding: 0.5rem 1rem;
        border-radius: 4px;
        cursor: pointer;
        margin-top: 0.5rem;
    `;

    button.addEventListener('click', function() {
        // Placeholder for visualization logic
        alert('Visualization feature coming soon!');
    });

    element.appendChild(button);
}

function initializeEducationalFeatures() {
    // Add smooth scrolling for learning pathway
    const pathwaySteps = document.querySelectorAll('.pathway-step');
    pathwaySteps.forEach((step, index) => {
        step.addEventListener('click', function() {
            this.classList.toggle('expanded');
        });
    });

    // Add concept highlighting
    const conceptCards = document.querySelectorAll('.concept-card');
    conceptCards.forEach(card => {
        card.addEventListener('mouseenter', function() {
            this.style.transform = 'translateY(-2px)';
            this.style.boxShadow = '0 4px 8px rgba(0,0,0,0.1)';
        });

        card.addEventListener('mouseleave', function() {
            this.style.transform = 'translateY(0)';
            this.style.boxShadow = 'none';
        });
    });

    // Add progress tracking
    trackLearningProgress();
}

function trackLearningProgress() {
    const declarations = document.querySelectorAll('.educational-declaration');
    let viewedCount = 0;

    const observer = new IntersectionObserver((entries) => {
        entries.forEach(entry => {
            if (entry.isIntersecting) {
                entry.target.classList.add('viewed');
                viewedCount++;
                updateProgressIndicator(viewedCount, declarations.length);
            }
        });
    });

    declarations.forEach(decl => {
        observer.observe(decl);
    });
}

function updateProgressIndicator(viewed, total) {
    let indicator = document.querySelector('.progress-indicator');
    if (!indicator) {
        indicator = document.createElement('div');
        indicator.className = 'progress-indicator';
        indicator.style.cssText = `
            position: fixed;
            top: 10px;
            right: 10px;
            background: #3498db;
            color: white;
            padding: 0.5rem 1rem;
            border-radius: 4px;
            z-index: 1000;
        `;
        document.body.appendChild(indicator);
    }

    indicator.textContent = `Progress: ${viewed}/${total} theorems viewed`;
}
        """
