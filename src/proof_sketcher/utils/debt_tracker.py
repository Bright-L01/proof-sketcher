"""
Technical debt tracking system.
Provides programmatic tracking of technical debt items.
"""

import json
import logging
from dataclasses import asdict, dataclass, field
from datetime import datetime
from enum import Enum
from pathlib import Path
from typing import Any, Dict, List, Optional


class DebtPriority(Enum):
    """Priority levels for technical debt items."""

    P0_CRITICAL = "P0"  # Immediate action required
    P1_HIGH = "P1"  # Week 1-2
    P2_MEDIUM = "P2"  # Week 3-4
    P3_LOW = "P3"  # Week 5-6


class DebtCategory(Enum):
    """Categories of technical debt."""

    SECURITY = "security"
    FUNCTIONALITY = "functionality"
    TESTING = "testing"
    DOCUMENTATION = "documentation"
    PERFORMANCE = "performance"
    CODE_QUALITY = "code_quality"
    ARCHITECTURE = "architecture"
    DEPENDENCIES = "dependencies"


class DebtStatus(Enum):
    """Status of debt items."""

    OPEN = "open"
    IN_PROGRESS = "in_progress"
    FIXED = "fixed"
    WONT_FIX = "wont_fix"
    DEFERRED = "deferred"


@dataclass
class DebtItem:
    """Represents a single technical debt item."""

    id: str
    title: str
    description: str
    component: str
    category: DebtCategory
    priority: DebtPriority
    status: DebtStatus
    impact: str
    fix_required: str
    estimated_hours: int
    created_date: str = field(default_factory=lambda: datetime.now().isoformat())
    updated_date: str = field(default_factory=lambda: datetime.now().isoformat())
    fixed_date: Optional[str] = None
    tags: List[str] = field(default_factory=list)

    def to_dict(self) -> Dict[str, Any]:
        """Convert to dictionary for serialization."""
        data = asdict(self)
        data["category"] = self.category.value
        data["priority"] = self.priority.value
        data["status"] = self.status.value
        return data

    @classmethod
    def from_dict(cls, data: Dict[str, Any]) -> "DebtItem":
        """Create from dictionary."""
        data["category"] = DebtCategory(data["category"])
        data["priority"] = DebtPriority(data["priority"])
        data["status"] = DebtStatus(data["status"])
        return cls(**data)


class TechnicalDebtTracker:
    """Tracks and manages technical debt items."""

    def __init__(self, debt_file: Optional[Path] = None):
        """Initialize the debt tracker.

        Args:
            debt_file: Path to JSON file storing debt items
        """
        self.logger = logging.getLogger(__name__)
        self.debt_file = debt_file or Path("technical_debt.json")
        self.debt_items: List[DebtItem] = []
        self._load_debt_items()

    def _load_debt_items(self) -> None:
        """Load debt items from file."""
        if self.debt_file.exists():
            try:
                with open(self.debt_file, "r") as f:
                    data = json.load(f)
                    self.debt_items = [
                        DebtItem.from_dict(item) for item in data.get("items", [])
                    ]
                self.logger.info(f"Loaded {len(self.debt_items)} debt items")
            except Exception as e:
                self.logger.error(f"Failed to load debt items: {e}")
                self.debt_items = []

    def _save_debt_items(self) -> None:
        """Save debt items to file."""
        try:
            data = {
                "last_updated": datetime.now().isoformat(),
                "total_items": len(self.debt_items),
                "items": [item.to_dict() for item in self.debt_items],
            }
            with open(self.debt_file, "w") as f:
                json.dump(data, f, indent=2)
            self.logger.info(f"Saved {len(self.debt_items)} debt items")
        except Exception as e:
            self.logger.error(f"Failed to save debt items: {e}")

    def add_item(self, item: DebtItem) -> None:
        """Add a new debt item.

        Args:
            item: Debt item to add
        """
        # Check for duplicate ID
        if any(existing.id == item.id for existing in self.debt_items):
            raise ValueError(f"Debt item with ID '{item.id}' already exists")

        self.debt_items.append(item)
        self._save_debt_items()
        self.logger.info(f"Added debt item: {item.id}")

    def update_item(self, item_id: str, **updates) -> Optional[DebtItem]:
        """Update an existing debt item.

        Args:
            item_id: ID of item to update
            **updates: Fields to update

        Returns:
            Updated item or None if not found
        """
        for item in self.debt_items:
            if item.id == item_id:
                # Update fields
                for key, value in updates.items():
                    if hasattr(item, key):
                        # Handle enum conversions
                        if key == "category" and isinstance(value, str):
                            value = DebtCategory(value)
                        elif key == "priority" and isinstance(value, str):
                            value = DebtPriority(value)
                        elif key == "status" and isinstance(value, str):
                            value = DebtStatus(value)

                        setattr(item, key, value)

                # Update timestamp
                item.updated_date = datetime.now().isoformat()

                # Set fixed date if status changed to fixed
                if updates.get("status") == DebtStatus.FIXED:
                    item.fixed_date = datetime.now().isoformat()

                self._save_debt_items()
                self.logger.info(f"Updated debt item: {item_id}")
                return item

        self.logger.warning(f"Debt item not found: {item_id}")
        return None

    def get_item(self, item_id: str) -> Optional[DebtItem]:
        """Get a debt item by ID.

        Args:
            item_id: ID of item to retrieve

        Returns:
            Debt item or None if not found
        """
        for item in self.debt_items:
            if item.id == item_id:
                return item
        return None

    def get_items_by_status(self, status: DebtStatus) -> List[DebtItem]:
        """Get all items with a specific status.

        Args:
            status: Status to filter by

        Returns:
            List of matching items
        """
        return [item for item in self.debt_items if item.status == status]

    def get_items_by_priority(self, priority: DebtPriority) -> List[DebtItem]:
        """Get all items with a specific priority.

        Args:
            priority: Priority to filter by

        Returns:
            List of matching items
        """
        return [item for item in self.debt_items if item.priority == priority]

    def get_items_by_category(self, category: DebtCategory) -> List[DebtItem]:
        """Get all items in a specific category.

        Args:
            category: Category to filter by

        Returns:
            List of matching items
        """
        return [item for item in self.debt_items if item.category == category]

    def get_items_by_component(self, component: str) -> List[DebtItem]:
        """Get all items for a specific component.

        Args:
            component: Component name

        Returns:
            List of matching items
        """
        return [
            item
            for item in self.debt_items
            if item.component.lower() == component.lower()
        ]

    def get_summary(self) -> Dict[str, Any]:
        """Get summary statistics of technical debt.

        Returns:
            Dictionary with summary statistics
        """
        total_items = len(self.debt_items)
        open_items = len(self.get_items_by_status(DebtStatus.OPEN))
        in_progress = len(self.get_items_by_status(DebtStatus.IN_PROGRESS))
        fixed_items = len(self.get_items_by_status(DebtStatus.FIXED))

        # Calculate by priority
        priority_counts = {
            priority.value: len(self.get_items_by_priority(priority))
            for priority in DebtPriority
        }

        # Calculate by category
        category_counts = {
            category.value: len(self.get_items_by_category(category))
            for category in DebtCategory
        }

        # Calculate total estimated hours
        total_hours = sum(
            item.estimated_hours
            for item in self.debt_items
            if item.status != DebtStatus.FIXED
        )

        return {
            "total_items": total_items,
            "open_items": open_items,
            "in_progress_items": in_progress,
            "fixed_items": fixed_items,
            "priority_breakdown": priority_counts,
            "category_breakdown": category_counts,
            "total_estimated_hours": total_hours,
            "estimated_weeks": total_hours / 40,  # Assuming 40 hour work week
        }

    def generate_report(self) -> str:
        """Generate a markdown report of current technical debt.

        Returns:
            Markdown formatted report
        """
        summary = self.get_summary()

        report = ["# Technical Debt Report"]
        report.append(f"\n**Generated**: {datetime.now().isoformat()}")
        report.append(f"\n## Summary")
        report.append(f"- Total Items: {summary['total_items']}")
        report.append(f"- Open Items: {summary['open_items']}")
        report.append(f"- In Progress: {summary['in_progress_items']}")
        report.append(f"- Fixed Items: {summary['fixed_items']}")
        report.append(f"- Estimated Hours: {summary['total_estimated_hours']}")
        report.append(f"- Estimated Weeks: {summary['estimated_weeks']:.1f}")

        # Priority breakdown
        report.append(f"\n## Priority Breakdown")
        for priority, count in summary["priority_breakdown"].items():
            if count > 0:
                report.append(f"- {priority}: {count}")

        # Category breakdown
        report.append(f"\n## Category Breakdown")
        for category, count in summary["category_breakdown"].items():
            if count > 0:
                report.append(f"- {category}: {count}")

        # Detailed items by priority
        for priority in DebtPriority:
            items = self.get_items_by_priority(priority)
            if items:
                report.append(f"\n## {priority.value} Priority Items")
                for item in items:
                    if item.status != DebtStatus.FIXED:
                        status_emoji = {
                            DebtStatus.OPEN: "🔴",
                            DebtStatus.IN_PROGRESS: "🟡",
                            DebtStatus.DEFERRED: "🔵",
                        }.get(item.status, "⚪")

                        report.append(f"\n### {status_emoji} {item.title}")
                        report.append(f"- **ID**: {item.id}")
                        report.append(f"- **Component**: {item.component}")
                        report.append(f"- **Category**: {item.category.value}")
                        report.append(f"- **Impact**: {item.impact}")
                        report.append(f"- **Estimated Hours**: {item.estimated_hours}")
                        report.append(f"- **Description**: {item.description}")
                        report.append(f"- **Fix Required**: {item.fix_required}")

        return "\n".join(report)


# Initialize default tracker when module is imported
default_tracker = TechnicalDebtTracker()


def create_initial_debt_items():
    """Create the initial set of debt items based on current assessment."""
    items = [
        DebtItem(
            id="DEBT-001",
            title="Empty Theorem Statements",
            description="parse_theorems() returns empty statements for all theorems",
            component="Parser",
            category=DebtCategory.FUNCTIONALITY,
            priority=DebtPriority.P0_CRITICAL,
            status=DebtStatus.OPEN,
            impact="Core functionality broken - blocks all theorem processing",
            fix_required="Rewrite Lean integration using proper FFI or server mode",
            estimated_hours=40,
            tags=["blocker", "core"],
        ),
        DebtItem(
            id="DEBT-002",
            title="Security Vulnerabilities",
            description="69 total vulnerabilities including 6 HIGH severity",
            component="Core",
            category=DebtCategory.SECURITY,
            priority=DebtPriority.P0_CRITICAL,
            status=DebtStatus.IN_PROGRESS,
            impact="Production deployment blocked",
            fix_required="Update dependencies and fix remaining MEDIUM issues",
            estimated_hours=20,
            tags=["security", "blocker"],
        ),
        DebtItem(
            id="DEBT-003",
            title="Test Coverage Crisis",
            description="Only 11% test coverage vs 90% target",
            component="All",
            category=DebtCategory.TESTING,
            priority=DebtPriority.P0_CRITICAL,
            status=DebtStatus.OPEN,
            impact="Cannot verify functionality or prevent regressions",
            fix_required="Write comprehensive unit and integration tests",
            estimated_hours=160,
            tags=["quality", "testing"],
        ),
        DebtItem(
            id="DEBT-004",
            title="MCP Integration Failure",
            description="Manim MCP server connection fails with no error handling",
            component="Animator",
            category=DebtCategory.FUNCTIONALITY,
            priority=DebtPriority.P1_HIGH,
            status=DebtStatus.OPEN,
            impact="Animation generation broken",
            fix_required="Implement MCP connection retry and fallback logic",
            estimated_hours=30,
            tags=["integration", "animation"],
        ),
        DebtItem(
            id="DEBT-005",
            title="Code Quality Violations",
            description="3,625 linting violations across codebase",
            component="All",
            category=DebtCategory.CODE_QUALITY,
            priority=DebtPriority.P1_HIGH,
            status=DebtStatus.OPEN,
            impact="Maintainability crisis",
            fix_required="Fix linting issues and enforce in CI/CD",
            estimated_hours=40,
            tags=["quality", "maintainability"],
        ),
    ]

    for item in items:
        try:
            default_tracker.add_item(item)
        except ValueError:
            # Item already exists
            pass


if __name__ == "__main__":
    # Example usage
    create_initial_debt_items()
    print(default_tracker.generate_report())
