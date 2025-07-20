#!/usr/bin/env python3
"""
Final Comprehensive Performance Test and University Readiness Assessment

This script provides the definitive answer on whether proof-sketcher is ready
for university-scale deployment.
"""

from __future__ import annotations

import json
import statistics
import sys
import threading
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Dict, List

import psutil

# Add project root to path
project_root = Path(__file__).parent
sys.path.insert(0, str(project_root / "src"))

from proof_sketcher.generator.offline import OfflineGenerator
from proof_sketcher.parser.simple_parser import SimpleLeanParser


@dataclass
class PerformanceData:
    """Container for performance measurements"""

    operation: str
    start_time: float
    end_time: float
    memory_start_mb: float
    memory_peak_mb: float
    success: bool
    items_processed: int
    errors: List[str]

    @property
    def duration(self) -> float:
        return self.end_time - self.start_time

    @property
    def throughput(self) -> float:
        return self.items_processed / max(self.duration, 0.001)

    @property
    def memory_used_mb(self) -> float:
        return self.memory_peak_mb - self.memory_start_mb


class UniversityPerformanceTester:
    """Comprehensive university performance tester"""

    def __init__(self):
        self.process = psutil.Process()
        self.test_files = [
            project_root / "tests/data/university_scale_basic.lean",
            project_root / "tests/data/university_scale_intermediate.lean",
            project_root / "tests/data/university_scale_advanced.lean",
        ]
        self.results = []

    def get_memory_usage(self) -> float:
        """Get current memory usage in MB"""
        return self.process.memory_info().rss / 1024 / 1024

    def test_single_file_performance(self) -> Dict[str, PerformanceData]:
        """Test single file parsing and generation performance"""
        print("\n📊 Testing Single File Performance")
        print("-" * 50)

        results = {}

        for test_file in self.test_files:
            if not test_file.exists():
                continue

            print(f"Testing: {test_file.name}")

            memory_start = self.get_memory_usage()
            start_time = time.time()
            memory_peak = memory_start
            errors = []

            try:
                # Parse file
                parser = SimpleLeanParser()
                parse_result = parser.parse_file(test_file)

                if not parse_result.success:
                    errors.append("Parse failed")
                    theorems = []
                else:
                    theorems = parse_result.theorems

                # Generate sketches
                generator = OfflineGenerator()
                successful_generations = 0

                for theorem in theorems:
                    try:
                        sketch = generator.generate_proof_sketch(theorem)
                        if (
                            sketch and sketch.intuitive_overview
                        ):  # Check for valid content
                            successful_generations += 1
                        memory_peak = max(memory_peak, self.get_memory_usage())
                    except Exception as e:
                        errors.append(f"Generation failed for {theorem.name}: {e}")

                end_time = time.time()

                performance = PerformanceData(
                    operation=f"single_file_{test_file.stem}",
                    start_time=start_time,
                    end_time=end_time,
                    memory_start_mb=memory_start,
                    memory_peak_mb=memory_peak,
                    success=successful_generations > 0,
                    items_processed=successful_generations,
                    errors=errors,
                )

                results[test_file.stem] = performance

                print(f"  Theorems parsed: {len(theorems)}")
                print(f"  Successful generations: {successful_generations}")
                print(f"  Time: {performance.duration:.3f}s")
                print(f"  Throughput: {performance.throughput:.1f} theorems/sec")
                print(f"  Memory: {performance.memory_used_mb:.1f}MB")

            except Exception as e:
                end_time = time.time()
                performance = PerformanceData(
                    operation=f"single_file_{test_file.stem}_FAILED",
                    start_time=start_time,
                    end_time=end_time,
                    memory_start_mb=memory_start,
                    memory_peak_mb=self.get_memory_usage(),
                    success=False,
                    items_processed=0,
                    errors=[str(e)],
                )
                results[test_file.stem] = performance
                print(f"  FAILED: {e}")

        return results

    def simulate_student_workload(
        self, student_id: int, duration: int = 20
    ) -> PerformanceData:
        """Simulate a single student's workload"""
        memory_start = self.get_memory_usage()
        start_time = time.time()
        memory_peak = memory_start
        errors = []
        theorems_processed = 0

        parser = SimpleLeanParser()
        generator = OfflineGenerator()

        # Student works for specified duration
        end_target = start_time + duration

        while time.time() < end_target:
            for test_file in self.test_files:
                if not test_file.exists() or time.time() >= end_target:
                    break

                try:
                    # Parse file (student opens file)
                    result = parser.parse_file(test_file)
                    if result.success:
                        # Work on first few theorems (typical student behavior)
                        for theorem in result.theorems[:3]:
                            try:
                                sketch = generator.generate_proof_sketch(theorem)
                                if sketch and sketch.intuitive_overview:
                                    theorems_processed += 1
                                memory_peak = max(memory_peak, self.get_memory_usage())

                                # Simulate thinking time
                                time.sleep(0.05)

                                if time.time() >= end_target:
                                    break
                            except Exception as e:
                                errors.append(
                                    f"Student {student_id} generation error: {e}"
                                )

                except Exception as e:
                    errors.append(f"Student {student_id} parse error: {e}")

        end_time = time.time()

        return PerformanceData(
            operation=f"student_{student_id}",
            start_time=start_time,
            end_time=end_time,
            memory_start_mb=memory_start,
            memory_peak_mb=memory_peak,
            success=theorems_processed > 0,
            items_processed=theorems_processed,
            errors=errors,
        )

    def test_concurrent_classroom(
        self, num_students: int, session_duration: int = 20
    ) -> Dict[str, Any]:
        """Test concurrent classroom simulation"""
        print(f"\n👥 Testing Concurrent Classroom: {num_students} students")
        print("-" * 50)

        overall_start = time.time()
        overall_memory_start = self.get_memory_usage()

        student_results = []
        failed_students = 0

        # Run concurrent student simulations
        with ThreadPoolExecutor(max_workers=min(num_students, 25)) as executor:
            futures = [
                executor.submit(
                    self.simulate_student_workload, student_id, session_duration
                )
                for student_id in range(num_students)
            ]

            for future in as_completed(futures):
                try:
                    result = future.result(timeout=session_duration + 10)
                    student_results.append(result)
                except Exception as e:
                    failed_students += 1
                    print(f"Student failed: {e}")

        overall_end = time.time()
        overall_memory_peak = self.get_memory_usage()

        # Calculate statistics
        successful_students = [r for r in student_results if r.success]
        total_theorems = sum(r.items_processed for r in student_results)

        avg_theorems_per_student = (
            statistics.mean([r.items_processed for r in student_results])
            if student_results
            else 0
        )
        avg_student_time = (
            statistics.mean([r.duration for r in student_results])
            if student_results
            else 0
        )
        system_throughput = (
            total_theorems / (overall_end - overall_start)
            if (overall_end - overall_start) > 0
            else 0
        )

        success_rate = len(successful_students) / max(num_students, 1)

        result = {
            "num_students": num_students,
            "session_duration": session_duration,
            "successful_students": len(successful_students),
            "failed_students": failed_students,
            "success_rate": success_rate,
            "total_theorems_processed": total_theorems,
            "avg_theorems_per_student": avg_theorems_per_student,
            "avg_student_session_time": avg_student_time,
            "system_throughput_theorems_per_sec": system_throughput,
            "total_test_time": overall_end - overall_start,
            "memory_increase_mb": overall_memory_peak - overall_memory_start,
            "status": "PASSED" if success_rate >= 0.8 else "FAILED",
        }

        print(
            f"  Successful students: {len(successful_students)}/{num_students} ({success_rate:.1%})"
        )
        print(f"  Total theorems processed: {total_theorems}")
        print(f"  Average theorems/student: {avg_theorems_per_student:.1f}")
        print(f"  System throughput: {system_throughput:.2f} theorems/sec")
        print(f"  Memory increase: {result['memory_increase_mb']:.1f}MB")
        print(f"  Status: {result['status']}")

        return result

    def run_scalability_test(self) -> Dict[str, Any]:
        """Test system scalability with increasing load"""
        print(f"\n📈 Testing System Scalability")
        print("-" * 50)

        test_sizes = [5, 10, 20, 30, 40, 50]
        scalability_results = []

        for size in test_sizes:
            print(f"\nTesting {size} concurrent students...")
            result = self.test_concurrent_classroom(
                size, 15
            )  # Shorter sessions for scalability test
            scalability_results.append(result)

            # Stop if we hit a failure threshold
            if result["success_rate"] < 0.5:
                print(
                    f"⚠️ Stopping scalability test - success rate too low at {size} students"
                )
                break

        # Find maximum viable capacity
        successful_tests = [r for r in scalability_results if r["status"] == "PASSED"]
        max_capacity = (
            max([r["num_students"] for r in successful_tests])
            if successful_tests
            else 0
        )

        return {
            "test_results": scalability_results,
            "max_viable_capacity": max_capacity,
            "scalability_summary": {
                "tests_run": len(scalability_results),
                "tests_passed": len(successful_tests),
                "max_students_80_percent_success": max_capacity,
            },
        }

    def assess_university_readiness(
        self, single_file_results: Dict, scalability_results: Dict
    ) -> Dict[str, Any]:
        """Comprehensive university readiness assessment"""
        print(f"\n🎓 UNIVERSITY READINESS ASSESSMENT")
        print("=" * 60)

        assessment = {
            "overall_grade": None,
            "production_ready": False,
            "university_scale_ready": False,
            "classroom_ready": False,
            "recommendations": [],
            "capacity_analysis": {},
            "performance_analysis": {},
            "bottlenecks": [],
        }

        # Analyze single file performance
        successful_single_tests = [r for r in single_file_results.values() if r.success]
        if successful_single_tests:
            avg_single_throughput = statistics.mean(
                [r.throughput for r in successful_single_tests]
            )
            max_memory_single = max([r.memory_used_mb for r in successful_single_tests])

            assessment["performance_analysis"] = {
                "avg_single_file_throughput": avg_single_throughput,
                "max_single_file_memory_mb": max_memory_single,
                "single_file_tests_passed": len(successful_single_tests),
                "single_file_tests_total": len(single_file_results),
            }

            # Performance criteria
            if avg_single_throughput < 1.0:
                assessment["bottlenecks"].append("Low single-file throughput")
            if max_memory_single > 100:
                assessment["bottlenecks"].append("High memory usage per file")
        else:
            assessment["bottlenecks"].append("Single file processing failures")

        # Analyze scalability
        max_capacity = scalability_results["max_viable_capacity"]
        scalability_data = scalability_results["scalability_summary"]

        assessment["capacity_analysis"] = {
            "max_concurrent_students": max_capacity,
            "scalability_tests_passed": scalability_data["tests_passed"],
            "scalability_tests_total": scalability_data["tests_run"],
        }

        # University readiness criteria
        if max_capacity >= 30:
            assessment["classroom_ready"] = True
        if max_capacity >= 50 and len(successful_single_tests) > 0:
            assessment["university_scale_ready"] = True
        if (
            assessment["classroom_ready"]
            and len(assessment["bottlenecks"]) <= 2
            and scalability_data["tests_passed"]
            >= scalability_data["tests_total"] * 0.7
        ):
            assessment["production_ready"] = True

        # Overall grading
        score = 0
        if assessment["production_ready"]:
            score += 40
        if assessment["university_scale_ready"]:
            score += 30
        if assessment["classroom_ready"]:
            score += 20
        if len(assessment["bottlenecks"]) == 0:
            score += 10

        if score >= 90:
            assessment["overall_grade"] = (
                "A - Excellent, ready for large-scale deployment"
            )
        elif score >= 80:
            assessment["overall_grade"] = (
                "B - Good, suitable for production with monitoring"
            )
        elif score >= 60:
            assessment["overall_grade"] = "C - Acceptable for small-scale deployment"
        elif score >= 40:
            assessment["overall_grade"] = "D - Limited deployment capability"
        else:
            assessment["overall_grade"] = "F - Not ready for production deployment"

        # Recommendations
        if not assessment["production_ready"]:
            assessment["recommendations"].append(
                "Address performance bottlenecks before production"
            )
        if not assessment["university_scale_ready"]:
            assessment["recommendations"].append(
                "Optimize concurrent processing for larger classes"
            )
        if "Low single-file throughput" in assessment["bottlenecks"]:
            assessment["recommendations"].append(
                "Optimize proof sketch generation algorithms"
            )
        if "High memory usage per file" in assessment["bottlenecks"]:
            assessment["recommendations"].append(
                "Implement memory optimization and garbage collection"
            )

        return assessment

    def run_comprehensive_test(self) -> Dict[str, Any]:
        """Run the complete university performance test suite"""
        print("🚀 COMPREHENSIVE UNIVERSITY PERFORMANCE TEST")
        print("=" * 60)
        print("Testing proof-sketcher for university-scale deployment readiness...")

        start_time = time.time()

        # Test 1: Single file performance
        single_file_results = self.test_single_file_performance()

        # Test 2: Scalability analysis
        scalability_results = self.run_scalability_test()

        # Test 3: University readiness assessment
        assessment = self.assess_university_readiness(
            single_file_results, scalability_results
        )

        total_time = time.time() - start_time

        # Compile final report
        final_report = {
            "test_suite": "university_performance_test",
            "timestamp": time.strftime("%Y-%m-%d %H:%M:%S"),
            "total_test_time_seconds": total_time,
            "single_file_performance": {
                name: {
                    "operation": perf.operation,
                    "duration": perf.duration,
                    "throughput": perf.throughput,
                    "memory_used_mb": perf.memory_used_mb,
                    "success": perf.success,
                    "items_processed": perf.items_processed,
                    "error_count": len(perf.errors),
                }
                for name, perf in single_file_results.items()
            },
            "scalability_results": scalability_results,
            "university_readiness_assessment": assessment,
            "system_info": {
                "cpu_count": psutil.cpu_count(),
                "total_memory_gb": psutil.virtual_memory().total / (1024**3),
                "available_memory_gb": psutil.virtual_memory().available / (1024**3),
            },
        }

        return final_report

    def print_final_report(self, report: Dict[str, Any]):
        """Print human-readable final report"""
        assessment = report["university_readiness_assessment"]

        print(f"\n{'='*60}")
        print("🎯 FINAL UNIVERSITY READINESS REPORT")
        print(f"{'='*60}")

        print(f"\n📊 OVERALL GRADE: {assessment['overall_grade']}")

        print(f"\n✅ READINESS STATUS:")
        print(
            f"   Production Ready: {'✅ YES' if assessment['production_ready'] else '❌ NO'}"
        )
        print(
            f"   University Scale: {'✅ YES' if assessment['university_scale_ready'] else '❌ NO'}"
        )
        print(
            f"   Classroom Ready:  {'✅ YES' if assessment['classroom_ready'] else '❌ NO'}"
        )

        capacity = assessment["capacity_analysis"]
        print(f"\n📈 CAPACITY ANALYSIS:")
        print(f"   Maximum Concurrent Students: {capacity['max_concurrent_students']}")
        print(
            f"   Scalability Tests Passed: {capacity['scalability_tests_passed']}/{capacity['scalability_tests_total']}"
        )

        performance = assessment["performance_analysis"]
        if performance:
            print(f"\n⚡ PERFORMANCE METRICS:")
            print(
                f"   Average Throughput: {performance['avg_single_file_throughput']:.2f} theorems/sec"
            )
            print(
                f"   Memory Usage: {performance['max_single_file_memory_mb']:.1f}MB per file"
            )

        if assessment["bottlenecks"]:
            print(f"\n⚠️  BOTTLENECKS IDENTIFIED:")
            for bottleneck in assessment["bottlenecks"]:
                print(f"   • {bottleneck}")

        if assessment["recommendations"]:
            print(f"\n💡 RECOMMENDATIONS:")
            for rec in assessment["recommendations"]:
                print(f"   • {rec}")

        print(f"\n⏱️  Total Test Time: {report['total_test_time_seconds']:.1f} seconds")

        # VERDICT
        print(f"\n{'='*60}")
        if assessment["production_ready"]:
            print("🎉 VERDICT: READY FOR UNIVERSITY DEPLOYMENT")
        elif assessment["classroom_ready"]:
            print("⚠️  VERDICT: READY FOR LIMITED CLASSROOM USE")
        else:
            print("❌ VERDICT: NOT READY FOR UNIVERSITY DEPLOYMENT")
        print(f"{'='*60}")


def main():
    """Main test execution"""
    tester = UniversityPerformanceTester()

    try:
        report = tester.run_comprehensive_test()
        tester.print_final_report(report)

        # Save detailed report
        report_file = project_root / "university_performance_report.json"
        with open(report_file, "w") as f:
            json.dump(report, f, indent=2, default=str)
        print(f"\n📄 Detailed report saved to: {report_file}")

        # Return success based on readiness
        return report["university_readiness_assessment"]["classroom_ready"]

    except Exception as e:
        print(f"\n💥 Test suite failed: {e}")
        import traceback

        traceback.print_exc()
        return False


if __name__ == "__main__":
    success = main()
    sys.exit(0 if success else 1)
