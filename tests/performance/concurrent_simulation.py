#!/usr/bin/env python3
"""
Concurrent User Simulation - Tests classroom-scale concurrent usage
"""

from __future__ import annotations

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
class StudentResult:
    """Results from a single student simulation"""

    student_id: int
    files_processed: int
    theorems_processed: int
    total_time: float
    success_rate: float
    errors: List[str]


class ConcurrentSimulator:
    """Simulates concurrent student usage"""

    def __init__(self):
        self.test_files = [
            project_root / "tests/data/university_scale_basic.lean",
            project_root / "tests/data/university_scale_intermediate.lean",
            project_root / "tests/data/university_scale_advanced.lean",
        ]
        self.process = psutil.Process()

    def simulate_student_session(
        self, student_id: int, session_duration: int = 30
    ) -> StudentResult:
        """Simulate a single student's session"""
        print(f"Student {student_id}: Starting session")

        parser = SimpleLeanParser()
        generator = OfflineGenerator()

        start_time = time.time()
        files_processed = 0
        theorems_processed = 0
        successful_operations = 0
        total_operations = 0
        errors = []

        # Simulate student working for a certain duration
        while time.time() - start_time < session_duration:
            for test_file in self.test_files:
                if not test_file.exists():
                    continue

                try:
                    # Parse file (simulate student opening a file)
                    result = parser.parse_file(test_file)
                    if result.success:
                        files_processed += 1

                        # Process a few theorems (simulate student working through problems)
                        for i, theorem in enumerate(
                            result.theorems[:5]
                        ):  # Student works on 5 theorems
                            total_operations += 1
                            try:
                                sketch = generator.generate_proof_sketch(theorem)
                                if sketch:
                                    successful_operations += 1
                                    theorems_processed += 1

                                # Simulate student thinking time
                                time.sleep(0.1)

                            except Exception as e:
                                errors.append(
                                    f"Generation failed for {theorem.name}: {e}"
                                )

                    # Break if session time exceeded
                    if time.time() - start_time >= session_duration:
                        break

                except Exception as e:
                    errors.append(f"Parse failed for {test_file.name}: {e}")

                # Break if session time exceeded
                if time.time() - start_time >= session_duration:
                    break

        total_time = time.time() - start_time
        success_rate = successful_operations / max(total_operations, 1)

        print(
            f"Student {student_id}: Completed session - {theorems_processed} theorems, {success_rate:.1%} success"
        )

        return StudentResult(
            student_id=student_id,
            files_processed=files_processed,
            theorems_processed=theorems_processed,
            total_time=total_time,
            success_rate=success_rate,
            errors=errors,
        )

    def run_classroom_simulation(
        self, num_students: int, session_duration: int = 30
    ) -> Dict[str, Any]:
        """Simulate a classroom of students"""
        print(
            f"\n🏫 Simulating classroom with {num_students} students for {session_duration}s each"
        )

        baseline_memory = self.process.memory_info().rss / 1024 / 1024
        start_time = time.time()
        student_results = []
        failed_students = 0

        # Run students concurrently
        with ThreadPoolExecutor(max_workers=min(num_students, 20)) as executor:
            # Submit all student sessions
            futures = [
                executor.submit(
                    self.simulate_student_session, student_id, session_duration
                )
                for student_id in range(num_students)
            ]

            # Collect results
            for future in as_completed(futures):
                try:
                    result = future.result(timeout=session_duration + 10)
                    student_results.append(result)
                except Exception as e:
                    failed_students += 1
                    print(f"Student session failed: {e}")

        total_time = time.time() - start_time
        peak_memory = self.process.memory_info().rss / 1024 / 1024

        # Calculate statistics
        if student_results:
            total_theorems = sum(r.theorems_processed for r in student_results)
            avg_success_rate = statistics.mean(
                [r.success_rate for r in student_results]
            )
            avg_theorems_per_student = statistics.mean(
                [r.theorems_processed for r in student_results]
            )
            system_throughput = total_theorems / total_time if total_time > 0 else 0
        else:
            total_theorems = 0
            avg_success_rate = 0
            avg_theorems_per_student = 0
            system_throughput = 0

        return {
            "test_name": f"classroom_simulation_{num_students}_students",
            "num_students": num_students,
            "session_duration": session_duration,
            "total_time": total_time,
            "successful_students": len(student_results),
            "failed_students": failed_students,
            "total_theorems_processed": total_theorems,
            "avg_theorems_per_student": avg_theorems_per_student,
            "avg_success_rate": avg_success_rate,
            "system_throughput_theorems_per_second": system_throughput,
            "memory_baseline_mb": baseline_memory,
            "memory_peak_mb": peak_memory,
            "memory_increase_mb": peak_memory - baseline_memory,
            "student_results": [
                {
                    "student_id": r.student_id,
                    "theorems_processed": r.theorems_processed,
                    "success_rate": r.success_rate,
                    "errors": len(r.errors),
                }
                for r in student_results
            ],
        }


def main():
    """Run concurrent simulation tests"""
    print("🚀 Concurrent Student Simulation Test")
    print("=" * 50)

    simulator = ConcurrentSimulator()

    # Test different classroom sizes
    test_scenarios = [
        (5, 10),  # Small class, short session
        (10, 20),  # Medium class, medium session
        (20, 30),  # Large class, full session
        (35, 30),  # Very large class
        (50, 30),  # Maximum expected class size
    ]

    results = []

    for num_students, duration in test_scenarios:
        print(f"\n{'='*60}")
        print(f"Testing {num_students} students, {duration}s session")
        print(f"{'='*60}")

        try:
            result = simulator.run_classroom_simulation(num_students, duration)
            results.append(result)

            # Print summary
            print(f"\n📊 Results for {num_students} students:")
            print(f"  Success rate: {result['avg_success_rate']:.1%}")
            print(f"  Theorems/student: {result['avg_theorems_per_student']:.1f}")
            print(
                f"  System throughput: {result['system_throughput_theorems_per_second']:.2f} theorems/sec"
            )
            print(f"  Memory increase: {result['memory_increase_mb']:.1f} MB")
            print(f"  Failed students: {result['failed_students']}")

        except Exception as e:
            print(f"❌ Test failed: {e}")
            results.append(
                {"num_students": num_students, "error": str(e), "status": "FAILED"}
            )

    # Overall assessment
    print(f"\n{'='*60}")
    print("📈 OVERALL PERFORMANCE ASSESSMENT")
    print(f"{'='*60}")

    successful_tests = [r for r in results if "error" not in r]

    if successful_tests:
        max_successful_students = max(
            r["num_students"] for r in successful_tests if r["avg_success_rate"] >= 0.8
        )
        best_throughput = max(
            r["system_throughput_theorems_per_second"] for r in successful_tests
        )
        max_memory_increase = max(r["memory_increase_mb"] for r in successful_tests)

        print(
            f"✅ Maximum concurrent students (80%+ success): {max_successful_students}"
        )
        print(f"⚡ Best system throughput: {best_throughput:.2f} theorems/sec")
        print(f"🧠 Maximum memory increase: {max_memory_increase:.1f} MB")

        # University readiness assessment
        if max_successful_students >= 35 and best_throughput >= 1.0:
            grade = "A - Excellent for university deployment"
        elif max_successful_students >= 25 and best_throughput >= 0.5:
            grade = "B - Good for medium-size classes"
        elif max_successful_students >= 15:
            grade = "C - Suitable for small classes only"
        else:
            grade = "F - Not ready for classroom deployment"

        print(f"🎯 Overall Grade: {grade}")

        # Production recommendations
        print(f"\n💡 RECOMMENDATIONS:")
        if max_memory_increase > 500:
            print("  ⚠️  High memory usage - consider optimization")
        if max_successful_students < 30:
            print("  ⚠️  Limited concurrent capacity - not suitable for large classes")
        if best_throughput < 1.0:
            print("  ⚠️  Low throughput - students may experience delays")

    else:
        print("❌ All tests failed - system not ready for production")

    print(f"\n✅ Concurrent simulation test completed")
    return len(successful_tests) > 0


if __name__ == "__main__":
    success = main()
    sys.exit(0 if success else 1)
