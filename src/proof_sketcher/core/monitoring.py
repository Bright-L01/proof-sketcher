"""Production monitoring and health checks for Proof Sketcher.

This module provides comprehensive monitoring capabilities including health checks,
performance metrics, error tracking, and usage statistics.
"""

import asyncio
import ast
import json
import logging
import operator
import platform
import time
from collections import defaultdict, deque
from dataclasses import dataclass, field
from datetime import datetime, timedelta
from functools import reduce
from pathlib import Path
from typing import Any, Dict, List, Optional, Callable, Awaitable

import psutil

from .performance import global_monitor
from ..core.exceptions import ProofSketcherError


class MonitoringError(ProofSketcherError):
    """Monitoring-related errors."""
    pass


@dataclass
class HealthCheck:
    """Health check definition."""
    name: str
    description: str
    check_func: Callable[[], bool]
    critical: bool = True
    timeout: float = 5.0
    interval: float = 60.0
    last_run: float = 0.0
    last_result: Optional[bool] = None
    last_error: Optional[str] = None


@dataclass
class AlertRule:
    """Alert rule definition."""
    name: str
    condition: str  # Python expression
    threshold: float
    message: str
    severity: str = "warning"  # info, warning, error, critical
    cooldown: float = 300.0  # 5 minutes
    last_triggered: float = 0.0


@dataclass
class UsageMetrics:
    """Usage metrics tracking."""
    theorems_processed: int = 0
    files_processed: int = 0
    exports_generated: int = 0
    cache_hits: int = 0
    cache_misses: int = 0
    errors_encountered: int = 0
    processing_time_total: float = 0.0
    last_updated: float = field(default_factory=time.time)


class HealthMonitor:
    """Comprehensive health monitoring system."""
    
    def __init__(self, config_dir: Optional[Path] = None):
        """Initialize health monitor.
        
        Args:
            config_dir: Directory for monitoring configuration
        """
        self.config_dir = config_dir or Path.home() / ".proof-sketcher"
        self.config_dir.mkdir(parents=True, exist_ok=True)
        
        self.logger = logging.getLogger(__name__)
        
        # Health checks registry
        self.health_checks: Dict[str, HealthCheck] = {}
        
        # Alert rules registry
        self.alert_rules: Dict[str, AlertRule] = {}
        
        # Alert history
        self.alert_history: deque[Dict[str, Any]] = deque(maxlen=1000)
        
        # System metrics
        self.system_metrics: Dict[str, Any] = {}
        
        # Usage tracking
        self.usage_metrics = UsageMetrics()
        
        # Monitoring state
        self._monitoring_active = False
        self._monitoring_task: Optional[asyncio.Task[None]] = None
        
        # Initialize default health checks
        self._register_default_health_checks()
        self._register_default_alert_rules()
    
    def _register_default_health_checks(self) -> None:
        """Register default health checks."""
        
        def check_disk_space() -> bool:
            """Check if sufficient disk space is available."""
            try:
                disk_usage = psutil.disk_usage('/')
                free_percent = (disk_usage.free / disk_usage.total) * 100
                return free_percent > 10.0  # At least 10% free
            except Exception:
                return False
        
        def check_memory_usage() -> bool:
            """Check if memory usage is reasonable."""
            try:
                memory = psutil.virtual_memory()
                return memory.percent < 90.0  # Less than 90% used
            except Exception:
                return False
        
        def check_cache_directory() -> bool:
            """Check if cache directory is accessible."""
            try:
                cache_dir = self.config_dir / "cache"
                cache_dir.mkdir(exist_ok=True)
                test_file = cache_dir / ".health_check"
                test_file.write_text("test")
                test_file.unlink()
                return True
            except Exception:
                return False
        
        def check_lean_executable() -> bool:
            """Check if Lean executable is available."""
            try:
                import subprocess
                result = subprocess.run(
                    ["lean", "--version"],
                    capture_output=True,
                    timeout=5
                )
                return result.returncode == 0
            except Exception:
                return False
        
        # Register health checks
        self.register_health_check(
            "disk_space",
            "Sufficient disk space available",
            check_disk_space,
            critical=True
        )
        
        self.register_health_check(
            "memory_usage",
            "Memory usage within acceptable limits",
            check_memory_usage,
            critical=False
        )
        
        self.register_health_check(
            "cache_directory",
            "Cache directory is accessible",
            check_cache_directory,
            critical=True
        )
        
        self.register_health_check(
            "lean_executable",
            "Lean executable is available",
            check_lean_executable,
            critical=True
        )
    
    def _register_default_alert_rules(self) -> None:
        """Register default alert rules."""
        
        self.register_alert_rule(
            "high_error_rate",
            "error_rate > threshold",
            5.0,  # 5% error rate
            "High error rate detected: {error_rate:.1f}%",
            "warning"
        )
        
        self.register_alert_rule(
            "low_cache_hit_rate",
            "cache_hit_rate < threshold",
            0.5,  # 50% hit rate
            "Low cache hit rate: {cache_hit_rate:.1f}%",
            "info"
        )
        
        self.register_alert_rule(
            "high_memory_usage",
            "memory_percent > threshold",
            85.0,  # 85% memory usage
            "High memory usage: {memory_percent:.1f}%",
            "warning"
        )
        
        self.register_alert_rule(
            "slow_processing",
            "avg_processing_time > threshold",
            10.0,  # 10 seconds per theorem
            "Slow processing detected: {avg_processing_time:.1f}s per theorem",
            "warning"
        )
    
    def register_health_check(
        self,
        name: str,
        description: str,
        check_func: Callable[[], bool],
        critical: bool = True,
        timeout: float = 5.0,
        interval: float = 60.0
    ) -> None:
        """Register a health check.
        
        Args:
            name: Health check name
            description: Human-readable description
            check_func: Function that returns True if healthy
            critical: Whether this check is critical for system health
            timeout: Timeout for the check function
            interval: How often to run the check
        """
        self.health_checks[name] = HealthCheck(
            name=name,
            description=description,
            check_func=check_func,
            critical=critical,
            timeout=timeout,
            interval=interval
        )
    
    def register_alert_rule(
        self,
        name: str,
        condition: str,
        threshold: float,
        message: str,
        severity: str = "warning",
        cooldown: float = 300.0
    ) -> None:
        """Register an alert rule.
        
        Args:
            name: Alert rule name
            condition: Python expression for the condition
            threshold: Threshold value for the condition
            message: Alert message template
            severity: Alert severity level
            cooldown: Minimum time between alerts
        """
        self.alert_rules[name] = AlertRule(
            name=name,
            condition=condition,
            threshold=threshold,
            message=message,
            severity=severity,
            cooldown=cooldown
        )
    
    async def run_health_check(self, name: str) -> bool:
        """Run a specific health check.
        
        Args:
            name: Name of the health check
            
        Returns:
            True if healthy, False otherwise
        """
        if name not in self.health_checks:
            raise MonitoringError(f"Health check '{name}' not found")
        
        check = self.health_checks[name]
        
        try:
            # Run check with timeout
            result = await asyncio.wait_for(
                asyncio.get_event_loop().run_in_executor(
                    None, check.check_func
                ),
                timeout=check.timeout
            )
            
            check.last_result = result
            check.last_run = time.time()
            check.last_error = None
            
            return result
            
        except asyncio.TimeoutError:
            check.last_result = False
            check.last_run = time.time()
            check.last_error = f"Health check timed out after {check.timeout}s"
            self.logger.error(f"Health check '{name}' timed out")
            return False
            
        except Exception as e:
            check.last_result = False
            check.last_run = time.time()
            check.last_error = str(e)
            self.logger.error(f"Health check '{name}' failed: {e}")
            return False
    
    async def run_all_health_checks(self) -> Dict[str, bool]:
        """Run all registered health checks.
        
        Returns:
            Dictionary of health check results
        """
        results = {}
        
        tasks = {
            name: self.run_health_check(name)
            for name in self.health_checks.keys()
        }
        
        for name, task in tasks.items():
            try:
                results[name] = await task
            except Exception as e:
                self.logger.error(f"Failed to run health check '{name}': {e}")
                results[name] = False
        
        return results
    
    def update_system_metrics(self) -> None:
        """Update system performance metrics."""
        try:
            # CPU metrics
            self.system_metrics["cpu_percent"] = psutil.cpu_percent(interval=1)
            self.system_metrics["cpu_count"] = psutil.cpu_count()
            
            # Memory metrics
            memory = psutil.virtual_memory()
            self.system_metrics["memory_total"] = memory.total
            self.system_metrics["memory_used"] = memory.used
            self.system_metrics["memory_available"] = memory.available
            self.system_metrics["memory_percent"] = memory.percent
            
            # Disk metrics
            disk = psutil.disk_usage('/')
            self.system_metrics["disk_total"] = disk.total
            self.system_metrics["disk_used"] = disk.used
            self.system_metrics["disk_free"] = disk.free
            self.system_metrics["disk_percent"] = (disk.used / disk.total) * 100
            
            # Process metrics
            process = psutil.Process()
            self.system_metrics["process_memory"] = process.memory_info().rss
            self.system_metrics["process_cpu_percent"] = process.cpu_percent()
            
            # System info
            self.system_metrics["platform"] = platform.platform()
            self.system_metrics["python_version"] = platform.python_version()
            self.system_metrics["timestamp"] = time.time()
            
        except Exception as e:
            self.logger.error(f"Failed to update system metrics: {e}")
    
    def update_usage_metrics(self, **kwargs: int) -> None:
        """Update usage metrics.
        
        Args:
            **kwargs: Metric updates (e.g., theorems_processed=1)
        """
        for key, value in kwargs.items():
            if hasattr(self.usage_metrics, key):
                current_value = getattr(self.usage_metrics, key)
                setattr(self.usage_metrics, key, current_value + value)
        
        self.usage_metrics.last_updated = time.time()
    
    def check_alert_rules(self) -> None:
        """Check all alert rules and trigger alerts if necessary."""
        current_time = time.time()
        
        # Prepare context for alert evaluation
        context = {
            "threshold": 0,  # Will be set per rule
            **self.system_metrics,
            **self.usage_metrics.__dict__
        }
        
        # Calculate derived metrics
        total_requests = context.get("cache_hits", 0) + context.get("cache_misses", 0)
        if total_requests > 0:
            context["cache_hit_rate"] = context.get("cache_hits", 0) / total_requests
        else:
            context["cache_hit_rate"] = 0
        
        if context.get("theorems_processed", 0) > 0 and context.get("errors_encountered", 0) > 0:
            context["error_rate"] = (context["errors_encountered"] / context["theorems_processed"]) * 100
        else:
            context["error_rate"] = 0
        
        if context.get("theorems_processed", 0) > 0 and context.get("processing_time_total", 0) > 0:
            context["avg_processing_time"] = context["processing_time_total"] / context["theorems_processed"]
        else:
            context["avg_processing_time"] = 0
        
        # Check each alert rule
        for rule in self.alert_rules.values():
            try:
                # Check cooldown
                if current_time - rule.last_triggered < rule.cooldown:
                    continue
                
                # Set threshold in context
                context["threshold"] = rule.threshold
                
                # Evaluate condition safely
                if self._safe_eval_condition(rule.condition, context):
                    # Trigger alert
                    alert = {
                        "timestamp": current_time,
                        "rule": rule.name,
                        "severity": rule.severity,
                        "message": rule.message.format(**context),
                        "context": dict(context)
                    }
                    
                    self.alert_history.append(alert)
                    rule.last_triggered = current_time
                    
                    # Log alert
                    log_level = {
                        "info": logging.INFO,
                        "warning": logging.WARNING,
                        "error": logging.ERROR,
                        "critical": logging.CRITICAL
                    }.get(rule.severity, logging.WARNING)
                    
                    self.logger.log(log_level, f"ALERT: {alert['message']}")
                    
            except Exception as e:
                self.logger.error(f"Failed to evaluate alert rule '{rule.name}': {e}")
    
    async def start_monitoring(self, interval: float = 30.0) -> None:
        """Start continuous monitoring.
        
        Args:
            interval: Monitoring interval in seconds
        """
        if self._monitoring_active:
            self.logger.warning("Monitoring is already active")
            return
        
        self._monitoring_active = True
        self._monitoring_task = asyncio.create_task(
            self._monitoring_loop(interval)
        )
        
        self.logger.info(f"Started monitoring with {interval}s interval")
    
    async def stop_monitoring(self) -> None:
        """Stop continuous monitoring."""
        if not self._monitoring_active:
            return
        
        self._monitoring_active = False
        
        if self._monitoring_task:
            self._monitoring_task.cancel()
            try:
                await self._monitoring_task
            except asyncio.CancelledError:
                pass
        
        self.logger.info("Stopped monitoring")
    
    async def _monitoring_loop(self, interval: float) -> None:
        """Main monitoring loop."""
        while self._monitoring_active:
            try:
                # Update system metrics
                self.update_system_metrics()
                
                # Run health checks that are due
                current_time = time.time()
                for check in self.health_checks.values():
                    if current_time - check.last_run >= check.interval:
                        await self.run_health_check(check.name)
                
                # Check alert rules
                self.check_alert_rules()
                
                # Record monitoring metrics
                global_monitor.record_metric(
                    "monitoring_cycle_completed",
                    current_time
                )
                
            except Exception as e:
                self.logger.error(f"Monitoring loop error: {e}")
            
            await asyncio.sleep(interval)
    
    def get_health_status(self) -> Dict[str, Any]:
        """Get comprehensive health status.
        
        Returns:
            Dictionary with health status information
        """
        # Overall health
        critical_checks = [
            check for check in self.health_checks.values()
            if check.critical
        ]
        
        critical_failing = [
            check for check in critical_checks
            if check.last_result is False
        ]
        
        overall_status = "healthy" if not critical_failing else "unhealthy"
        
        # Health check details
        health_checks = {}
        for name, check in self.health_checks.items():
            health_checks[name] = {
                "description": check.description,
                "status": "pass" if check.last_result else "fail",
                "last_run": check.last_run,
                "last_error": check.last_error,
                "critical": check.critical
            }
        
        # Recent alerts
        recent_alerts = [
            alert for alert in self.alert_history
            if time.time() - alert["timestamp"] < 3600  # Last hour
        ]
        
        return {
            "overall_status": overall_status,
            "timestamp": time.time(),
            "health_checks": health_checks,
            "system_metrics": self.system_metrics,
            "usage_metrics": self.usage_metrics.__dict__,
            "recent_alerts": list(recent_alerts),
            "alert_summary": {
                "total_alerts": len(self.alert_history),
                "recent_alerts": len(recent_alerts),
                "critical_alerts": len([a for a in recent_alerts if a["severity"] == "critical"])
            }
        }
    
    def _safe_eval_condition(self, condition: str, context: Dict[str, Any]) -> bool:
        """Safely evaluate a condition expression.
        
        Args:
            condition: Condition expression string
            context: Context dictionary for evaluation
            
        Returns:
            Boolean result of evaluation
        """
        # Define allowed operators
        ops = {
            ast.Add: operator.add,
            ast.Sub: operator.sub,
            ast.Mult: operator.mul,
            ast.Div: operator.truediv,
            ast.Lt: operator.lt,
            ast.LtE: operator.le,
            ast.Gt: operator.gt,
            ast.GtE: operator.ge,
            ast.Eq: operator.eq,
            ast.NotEq: operator.ne,
            ast.And: operator.and_,
            ast.Or: operator.or_,
        }
        
        try:
            # Parse expression
            tree = ast.parse(condition, mode='eval')
            
            def evaluate(node):
                if isinstance(node, ast.BoolOp):
                    op = ops[type(node.op)]
                    values = [evaluate(v) for v in node.values]
                    return reduce(op, values)
                elif isinstance(node, ast.Compare):
                    left = evaluate(node.left)
                    for op_node, comparator in zip(node.ops, node.comparators):
                        op = ops[type(op_node)]
                        right = evaluate(comparator)
                        if not op(left, right):
                            return False
                        left = right
                    return True
                elif isinstance(node, ast.BinOp):
                    return ops[type(node.op)](evaluate(node.left), evaluate(node.right))
                elif isinstance(node, ast.UnaryOp):
                    if isinstance(node.op, ast.Not):
                        return not evaluate(node.operand)
                    else:
                        raise ValueError(f"Unsupported unary operator: {type(node.op)}")
                elif isinstance(node, ast.Name):
                    return context.get(node.id, 0)
                elif isinstance(node, ast.Constant):
                    return node.value
                elif isinstance(node, ast.Num):  # Python < 3.8
                    return node.n
                elif isinstance(node, ast.Str):  # Python < 3.8
                    return node.s
                else:
                    raise ValueError(f"Unsupported node type: {type(node)}")
            
            return evaluate(tree.body)
            
        except Exception as e:
            self.logger.warning(f"Failed to evaluate condition '{condition}': {e}")
            return False
    
    def export_metrics(self, format_type: str = "json") -> str:
        """Export metrics in specified format.
        
        Args:
            format_type: Export format (json, prometheus)
            
        Returns:
            Formatted metrics string
        """
        if format_type.lower() == "json":
            return json.dumps(self.get_health_status(), indent=2, default=str)
        elif format_type.lower() == "prometheus":
            return self._export_prometheus_metrics()
        else:
            raise MonitoringError(f"Unsupported export format: {format_type}")
    
    def _export_prometheus_metrics(self) -> str:
        """Export metrics in Prometheus format."""
        lines = []
        
        # System metrics
        for key, value in self.system_metrics.items():
            if isinstance(value, (int, float)):
                lines.append(f"proof_sketcher_system_{key} {value}")
        
        # Usage metrics
        for key, value in self.usage_metrics.__dict__.items():
            if isinstance(value, (int, float)):
                lines.append(f"proof_sketcher_usage_{key} {value}")
        
        # Health check status
        for name, check in self.health_checks.items():
            status_value = 1 if check.last_result else 0
            lines.append(f'proof_sketcher_health_check{{name="{name}"}} {status_value}')
        
        return "\n".join(lines)


# Global monitoring instance
global_health_monitor = HealthMonitor()


def get_health_status() -> Dict[str, Any]:
    """Get current health status.
    
    Returns:
        Health status dictionary
    """
    return global_health_monitor.get_health_status()


def update_usage_metrics(**kwargs: int) -> None:
    """Update usage metrics.
    
    Args:
        **kwargs: Metric updates
    """
    global_health_monitor.update_usage_metrics(**kwargs)