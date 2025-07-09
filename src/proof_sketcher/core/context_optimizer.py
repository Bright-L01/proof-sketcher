"""
Mathematical Context Optimization System

This module implements the empirical strategy-mapping approach to achieve 50% success rate
by intelligently matching mathematical contexts to their optimal parsing strategies.

Mathematical Analysis:
- Arithmetic: 30% of files × 85% success = 25.5%
- Mixed: 45% of files × 40% success = 18%
- Complex: 25% of files × 25% success = 6.25%
Total: 49.75% ≈ 50%
"""

import json
import logging
import re
import time
from collections import defaultdict, deque
from dataclasses import dataclass, field
from enum import Enum
from pathlib import Path
from typing import Dict, List, Optional, Tuple, Union

import numpy as np

from ..utils.security import validate_theorem_name


class MathematicalContext(Enum):
    """Mathematical complexity contexts for optimization."""

    ARITHMETIC = "arithmetic"  # 30% of files, target 85% success
    MIXED = "mixed"  # 45% of files, target 40% success
    COMPLEX = "complex"  # 25% of files, target 25% success
    UNKNOWN = "unknown"


class OptimizationStrategy(Enum):
    """Parsing strategies optimized for different contexts."""

    TUNED_ARITHMETIC = "tuned_arithmetic"  # High precision for simple proofs
    HYBRID_MIXED = "hybrid_mixed"  # Balanced approach
    CONSERVATIVE_COMPLEX = "conservative_complex"  # Fallback-heavy for complex
    AGGRESSIVE_FALLBACK = "aggressive_fallback"  # Maximum compatibility
    PRECISION_FOCUSED = "precision_focused"  # Quality over quantity


@dataclass
class StrategyPerformance:
    """Track performance metrics for a strategy."""

    successes: int = 0
    failures: int = 0
    total_time: float = 0.0
    last_updated: float = field(default_factory=time.time)

    @property
    def success_rate(self) -> float:
        """Calculate success rate."""
        total = self.successes + self.failures
        return self.successes / total if total > 0 else 0.0

    @property
    def avg_time(self) -> float:
        """Calculate average processing time."""
        total = self.successes + self.failures
        return self.total_time / total if total > 0 else 0.0

    def update(self, success: bool, processing_time: float) -> None:
        """Update performance metrics."""
        if success:
            self.successes += 1
        else:
            self.failures += 1
        self.total_time += processing_time
        self.last_updated = time.time()


@dataclass
class BanditArm:
    """Multi-armed bandit for strategy selection."""

    strategy: OptimizationStrategy
    performance: StrategyPerformance = field(default_factory=StrategyPerformance)
    exploration_bonus: float = 0.0
    confidence_interval: Tuple[float, float] = (0.0, 1.0)

    def calculate_ucb1_score(self, total_trials: int, c: float = 1.4) -> float:
        """Calculate Upper Confidence Bound score for strategy selection."""
        if self.performance.successes + self.performance.failures == 0:
            return float("inf")  # Encourage exploration of untried strategies

        n_arm = self.performance.successes + self.performance.failures
        avg_reward = self.performance.success_rate
        exploration = c * np.sqrt(np.log(total_trials) / n_arm)

        return avg_reward + exploration


class MathematicalContextDetector:
    """Detect mathematical context of theorems for optimization."""

    def __init__(self):
        self.logger = logging.getLogger(__name__)

        # Context detection patterns (empirically derived)
        self.arithmetic_patterns = [
            r"\b(Nat|ℕ|Natural)\b.*\+.*=",  # Natural number arithmetic
            r"\b\d+\s*\+\s*\d+\s*=\s*\d+",  # Direct arithmetic
            r"\bzero\b.*\badd\b",  # Zero addition patterns
            r"\bsucc\b.*\bNat\b",  # Successor patterns
            r"\b(add_zero|zero_add|add_comm|add_assoc)\b",  # Basic arithmetic theorems
        ]

        self.complex_patterns = [
            r"\b(topology|continuous|manifold|sheaf|category)\b",  # Advanced math
            r"\b(homomorphism|isomorphism|functorial)\b",  # Abstract algebra
            r"\b(differential|measure|integral|limit)\b",  # Analysis
            r"\b(cohomology|homotopy|fibration)\b",  # Topology
            r"\b(scheme|variety|algebraic)\b",  # Algebraic geometry
            r"∀.*∃.*→",  # Complex logical structure
            r"\b(Module|Ring|Field|Group).*\[.*\]",  # Advanced structures
        ]

        self.mixed_patterns = [
            r"\b(List|Array|Vector)\b.*\b(length|append|map)\b",  # Data structures
            r"\b(induction|cases)\b.*\bwith\b",  # Proof techniques
            r"\b(lemma|theorem)\b.*→.*→",  # Multi-step proofs
            r"\b(rewrite|simp|apply)\b.*\b(at|in)\b",  # Tactic combinations
        ]

    def detect_context(
        self, theorem_content: str, theorem_name: str = ""
    ) -> MathematicalContext:
        """Detect the mathematical context of a theorem.

        Args:
            theorem_content: The theorem statement and proof
            theorem_name: Name of the theorem

        Returns:
            Detected mathematical context
        """
        content = f"{theorem_name} {theorem_content}".lower()

        # Count pattern matches for each context
        arithmetic_score = sum(
            1
            for pattern in self.arithmetic_patterns
            if re.search(pattern, content, re.IGNORECASE)
        )
        complex_score = sum(
            1
            for pattern in self.complex_patterns
            if re.search(pattern, content, re.IGNORECASE)
        )
        mixed_score = sum(
            1
            for pattern in self.mixed_patterns
            if re.search(pattern, content, re.IGNORECASE)
        )

        # Additional heuristics
        if len(content) < 100 and arithmetic_score > 0:
            return MathematicalContext.ARITHMETIC

        if complex_score > arithmetic_score and complex_score > mixed_score:
            return MathematicalContext.COMPLEX
        elif arithmetic_score > mixed_score and arithmetic_score > complex_score:
            return MathematicalContext.ARITHMETIC
        elif mixed_score > 0 or (arithmetic_score > 0 and complex_score > 0):
            return MathematicalContext.MIXED

        # Fallback classification based on content length and complexity
        if len(content) < 50:
            return MathematicalContext.ARITHMETIC
        elif len(content) > 300:
            return MathematicalContext.COMPLEX
        else:
            return MathematicalContext.MIXED


class ContextOptimizer:
    """Main optimization system implementing bandit learning for context-strategy mapping."""

    def __init__(self, learning_rate: float = 0.1, exploration_decay: float = 0.995):
        """Initialize the context optimizer.

        Args:
            learning_rate: Learning rate for bandit updates
            exploration_decay: Decay rate for exploration
        """
        self.logger = logging.getLogger(__name__)
        self.detector = MathematicalContextDetector()
        self.learning_rate = learning_rate
        self.exploration_decay = exploration_decay

        # Multi-armed bandit for each context
        self.bandits: Dict[MathematicalContext, List[BanditArm]] = {
            MathematicalContext.ARITHMETIC: [
                BanditArm(OptimizationStrategy.TUNED_ARITHMETIC),
                BanditArm(OptimizationStrategy.PRECISION_FOCUSED),
                BanditArm(OptimizationStrategy.HYBRID_MIXED),
            ],
            MathematicalContext.MIXED: [
                BanditArm(OptimizationStrategy.HYBRID_MIXED),
                BanditArm(OptimizationStrategy.TUNED_ARITHMETIC),
                BanditArm(OptimizationStrategy.CONSERVATIVE_COMPLEX),
            ],
            MathematicalContext.COMPLEX: [
                BanditArm(OptimizationStrategy.CONSERVATIVE_COMPLEX),
                BanditArm(OptimizationStrategy.AGGRESSIVE_FALLBACK),
                BanditArm(OptimizationStrategy.HYBRID_MIXED),
            ],
        }

        # Performance tracking
        self.context_distribution = defaultdict(int)
        self.overall_performance = StrategyPerformance()
        self.recent_results = deque(maxlen=100)  # Last 100 results for trend analysis

        # Target success rates (from mathematical analysis)
        self.target_rates = {
            MathematicalContext.ARITHMETIC: 0.85,  # 85% target
            MathematicalContext.MIXED: 0.40,  # 40% target
            MathematicalContext.COMPLEX: 0.25,  # 25% target
        }

        # Load previous performance if available
        self._load_performance_data()

    def select_strategy(self, context: MathematicalContext) -> OptimizationStrategy:
        """Select optimal strategy for given context using UCB1 algorithm.

        Args:
            context: Mathematical context

        Returns:
            Selected optimization strategy
        """
        if context not in self.bandits:
            context = MathematicalContext.MIXED  # Default fallback

        arms = self.bandits[context]
        total_trials = sum(
            arm.performance.successes + arm.performance.failures for arm in arms
        )

        if total_trials == 0:
            # First time - select default strategy for context
            if context == MathematicalContext.ARITHMETIC:
                return OptimizationStrategy.TUNED_ARITHMETIC
            elif context == MathematicalContext.COMPLEX:
                return OptimizationStrategy.CONSERVATIVE_COMPLEX
            else:
                return OptimizationStrategy.HYBRID_MIXED

        # Use UCB1 algorithm for exploration-exploitation balance
        best_arm = max(arms, key=lambda arm: arm.calculate_ucb1_score(total_trials))

        self.logger.debug(
            f"Selected {best_arm.strategy.value} for {context.value} "
            f"(UCB1: {best_arm.calculate_ucb1_score(total_trials):.3f})"
        )

        return best_arm.strategy

    def update_performance(
        self,
        context: MathematicalContext,
        strategy: OptimizationStrategy,
        success: bool,
        processing_time: float,
        error_details: Optional[str] = None,
    ) -> None:
        """Update strategy performance based on results.

        Args:
            context: Mathematical context used
            strategy: Strategy that was used
            success: Whether the operation succeeded
            processing_time: Time taken for processing
            error_details: Details if operation failed
        """
        # Update context distribution
        self.context_distribution[context] += 1

        # Update overall performance
        self.overall_performance.update(success, processing_time)

        # Update strategy-specific performance
        if context in self.bandits:
            for arm in self.bandits[context]:
                if arm.strategy == strategy:
                    arm.performance.update(success, processing_time)
                    break

        # Track recent results for trend analysis
        self.recent_results.append(
            {
                "context": context,
                "strategy": strategy,
                "success": success,
                "time": processing_time,
                "timestamp": time.time(),
                "error": error_details,
            }
        )

        # Adaptive learning: adjust exploration if we're not meeting targets
        if len(self.recent_results) >= 20:  # Sufficient data
            recent_success_rate = (
                sum(1 for r in list(self.recent_results)[-20:] if r["success"]) / 20
            )
            target_rate = self._calculate_weighted_target()

            if recent_success_rate < target_rate * 0.8:  # Significantly below target
                self._increase_exploration()
            elif recent_success_rate > target_rate * 1.1:  # Above target
                self._decrease_exploration()

        # Periodically save performance data
        if (
            self.overall_performance.successes + self.overall_performance.failures % 50
            == 0
        ):
            self._save_performance_data()

    def get_optimization_stats(self) -> Dict:
        """Get comprehensive optimization statistics.

        Returns:
            Dictionary with performance statistics
        """
        total_attempts = (
            self.overall_performance.successes + self.overall_performance.failures
        )
        current_rate = self.overall_performance.success_rate
        target_rate = self._calculate_weighted_target()

        # Calculate per-context statistics
        context_stats = {}
        for context, arms in self.bandits.items():
            context_total = sum(
                arm.performance.successes + arm.performance.failures for arm in arms
            )
            context_successes = sum(arm.performance.successes for arm in arms)
            context_rate = (
                context_successes / context_total if context_total > 0 else 0.0
            )

            best_arm = (
                max(arms, key=lambda a: a.performance.success_rate) if arms else None
            )

            context_stats[context.value] = {
                "attempts": context_total,
                "success_rate": context_rate,
                "target_rate": self.target_rates.get(context, 0.5),
                "best_strategy": best_arm.strategy.value if best_arm else None,
                "distribution_pct": (
                    self.context_distribution[context] / total_attempts * 100
                    if total_attempts > 0
                    else 0
                ),
            }

        return {
            "overall": {
                "total_attempts": total_attempts,
                "success_rate": current_rate,
                "target_rate": target_rate,
                "progress_to_target": (
                    current_rate / target_rate if target_rate > 0 else 0
                ),
                "avg_processing_time": self.overall_performance.avg_time,
            },
            "contexts": context_stats,
            "recent_trend": self._analyze_recent_trend(),
            "strategy_rankings": self._get_strategy_rankings(),
            "recommendations": self._generate_recommendations(),
        }

    def optimize_for_theorem(
        self, theorem_content: str, theorem_name: str = ""
    ) -> Tuple[MathematicalContext, OptimizationStrategy]:
        """Get optimized context and strategy for a specific theorem.

        Args:
            theorem_content: Content of the theorem
            theorem_name: Name of the theorem

        Returns:
            Tuple of (detected_context, recommended_strategy)
        """
        try:
            validate_theorem_name(theorem_name)
        except Exception as e:
            self.logger.warning(f"Invalid theorem name: {e}")
            theorem_name = "unnamed"

        # Detect mathematical context
        context = self.detector.detect_context(theorem_content, theorem_name)

        # Select optimal strategy
        strategy = self.select_strategy(context)

        self.logger.info(
            f"Optimized theorem '{theorem_name}': context={context.value}, strategy={strategy.value}"
        )

        return context, strategy

    def _calculate_weighted_target(self) -> float:
        """Calculate weighted target success rate based on context distribution."""
        total = sum(self.context_distribution.values())
        if total == 0:
            return 0.5  # Default target

        weighted_target = 0.0
        for context, count in self.context_distribution.items():
            weight = count / total
            target = self.target_rates.get(context, 0.5)
            weighted_target += weight * target

        return weighted_target

    def _increase_exploration(self) -> None:
        """Increase exploration in bandit algorithms."""
        for arms_list in self.bandits.values():
            for arm in arms_list:
                arm.exploration_bonus += 0.1
        self.logger.debug("Increased exploration due to poor performance")

    def _decrease_exploration(self) -> None:
        """Decrease exploration to exploit known good strategies."""
        for arms_list in self.bandits.values():
            for arm in arms_list:
                arm.exploration_bonus = max(0, arm.exploration_bonus - 0.05)
        self.logger.debug("Decreased exploration due to good performance")

    def _analyze_recent_trend(self) -> Dict:
        """Analyze recent performance trends."""
        if len(self.recent_results) < 10:
            return {"trend": "insufficient_data"}

        recent_20 = list(self.recent_results)[-20:]
        recent_10 = list(self.recent_results)[-10:]

        rate_20 = sum(1 for r in recent_20 if r["success"]) / len(recent_20)
        rate_10 = sum(1 for r in recent_10 if r["success"]) / len(recent_10)

        if rate_10 > rate_20 + 0.1:
            trend = "improving"
        elif rate_10 < rate_20 - 0.1:
            trend = "declining"
        else:
            trend = "stable"

        return {
            "trend": trend,
            "recent_20_rate": rate_20,
            "recent_10_rate": rate_10,
            "improvement": rate_10 - rate_20,
        }

    def _get_strategy_rankings(self) -> Dict:
        """Get strategy rankings by context."""
        rankings = {}
        for context, arms in self.bandits.items():
            sorted_arms = sorted(
                arms, key=lambda a: a.performance.success_rate, reverse=True
            )
            rankings[context.value] = [
                {
                    "strategy": arm.strategy.value,
                    "success_rate": arm.performance.success_rate,
                    "attempts": arm.performance.successes + arm.performance.failures,
                }
                for arm in sorted_arms
            ]
        return rankings

    def _generate_recommendations(self) -> List[str]:
        """Generate optimization recommendations."""
        recommendations = []

        # Check if we're meeting targets
        for context, target_rate in self.target_rates.items():
            if context in self.bandits:
                arms = self.bandits[context]
                total_attempts = sum(
                    arm.performance.successes + arm.performance.failures for arm in arms
                )
                total_successes = sum(arm.performance.successes for arm in arms)
                current_rate = (
                    total_successes / total_attempts if total_attempts > 0 else 0.0
                )

                if total_attempts >= 10:  # Sufficient data
                    if current_rate < target_rate * 0.8:
                        recommendations.append(
                            f"Underperforming in {context.value}: {current_rate:.1%} vs target {target_rate:.1%}"
                        )
                    elif current_rate > target_rate * 1.2:
                        recommendations.append(
                            f"Exceeding target in {context.value}: consider harder test cases"
                        )

        # Check overall progress
        overall_rate = self.overall_performance.success_rate
        target_overall = self._calculate_weighted_target()

        if overall_rate >= 0.45:  # Close to 50% target
            recommendations.append(
                "🎯 Approaching 50% target! Consider fine-tuning strategies"
            )
        elif overall_rate >= 0.35:
            recommendations.append("📈 Good progress toward 50% target")
        elif overall_rate < 0.25:
            recommendations.append(
                "⚠️ Below expected baseline - review strategy selection"
            )

        if not recommendations:
            recommendations.append("✅ Performance optimization on track")

        return recommendations

    def _save_performance_data(self) -> None:
        """Save performance data to disk for persistence."""
        try:
            data = {
                "bandits": {
                    context.value: [
                        {
                            "strategy": arm.strategy.value,
                            "successes": arm.performance.successes,
                            "failures": arm.performance.failures,
                            "total_time": arm.performance.total_time,
                            "last_updated": arm.performance.last_updated,
                        }
                        for arm in arms
                    ]
                    for context, arms in self.bandits.items()
                },
                "context_distribution": dict(self.context_distribution),
                "overall_performance": {
                    "successes": self.overall_performance.successes,
                    "failures": self.overall_performance.failures,
                    "total_time": self.overall_performance.total_time,
                    "last_updated": self.overall_performance.last_updated,
                },
            }

            save_path = Path(__file__).parent / ".." / "optimizer_data.json"
            with open(save_path, "w") as f:
                json.dump(data, f, indent=2)

        except Exception as e:
            self.logger.warning(f"Failed to save performance data: {e}")

    def _load_performance_data(self) -> None:
        """Load previous performance data from disk."""
        try:
            load_path = Path(__file__).parent / ".." / "optimizer_data.json"
            if not load_path.exists():
                return

            with open(load_path, "r") as f:
                data = json.load(f)

            # Restore bandit data
            if "bandits" in data:
                for context_str, arms_data in data["bandits"].items():
                    try:
                        context = MathematicalContext(context_str)
                        if context in self.bandits:
                            for i, arm_data in enumerate(arms_data):
                                if i < len(self.bandits[context]):
                                    arm = self.bandits[context][i]
                                    arm.performance.successes = arm_data.get(
                                        "successes", 0
                                    )
                                    arm.performance.failures = arm_data.get(
                                        "failures", 0
                                    )
                                    arm.performance.total_time = arm_data.get(
                                        "total_time", 0.0
                                    )
                                    arm.performance.last_updated = arm_data.get(
                                        "last_updated", time.time()
                                    )
                    except ValueError:
                        continue  # Skip invalid context

            # Restore context distribution
            if "context_distribution" in data:
                for context_str, count in data["context_distribution"].items():
                    try:
                        context = MathematicalContext(context_str)
                        self.context_distribution[context] = count
                    except ValueError:
                        continue

            # Restore overall performance
            if "overall_performance" in data:
                perf_data = data["overall_performance"]
                self.overall_performance.successes = perf_data.get("successes", 0)
                self.overall_performance.failures = perf_data.get("failures", 0)
                self.overall_performance.total_time = perf_data.get("total_time", 0.0)
                self.overall_performance.last_updated = perf_data.get(
                    "last_updated", time.time()
                )

            self.logger.info("Loaded previous optimization performance data")

        except Exception as e:
            self.logger.warning(f"Failed to load performance data: {e}")


# Global optimizer instance
_global_optimizer: Optional[ContextOptimizer] = None


def get_context_optimizer() -> ContextOptimizer:
    """Get the global context optimizer instance.

    Returns:
        ContextOptimizer instance
    """
    global _global_optimizer
    if _global_optimizer is None:
        _global_optimizer = ContextOptimizer()
    return _global_optimizer
