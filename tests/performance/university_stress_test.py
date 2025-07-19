#!/usr/bin/env python3
"""
University-Scale Stress Test for Proof-Sketcher

This script conducts comprehensive performance testing to evaluate if proof-sketcher
can handle university-scale deployments. Tests realistic classroom scenarios with
multiple students, large files, and concurrent processing.

Performance Claims to Validate:
- "Ready for production"
- "University-scale deployments" 
- "Mathlib-scale workloads"
- Classroom use (20-50 students)
"""

import asyncio
import json
import logging
import os
import resource
import statistics
import sys
import tempfile
import threading
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Tuple, Any
import psutil
import multiprocessing

# Add project root to path
project_root = Path(__file__).parent
sys.path.insert(0, str(project_root / "src"))

from proof_sketcher.cli.main import cli
from proof_sketcher.parser.simple_parser import SimpleLeanParser
from proof_sketcher.parser.config import ParserConfig
from proof_sketcher.generator.offline import OfflineGenerator
from proof_sketcher.exporter.batch_processor import BatchExporter
from proof_sketcher.exporter.models import ExportOptions
from proof_sketcher.config.config import ProofSketcherConfig

# Configure logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s'
)
logger = logging.getLogger(__name__)

@dataclass
class PerformanceMetrics:
    """Container for performance measurements"""
    operation: str
    file_size_mb: float
    theorem_count: int
    parse_time_seconds: float
    generation_time_seconds: float
    total_time_seconds: float
    memory_peak_mb: float
    memory_baseline_mb: float
    throughput_theorems_per_second: float
    success_rate: float
    errors: List[str]

@dataclass
class StressTestConfig:
    """Configuration for stress tests"""
    max_concurrent_students: int = 50
    max_file_size_mb: int = 10
    timeout_seconds: int = 300
    memory_limit_mb: int = 2048
    test_files: List[Path] = None

class UniversityStressTester:
    """Main stress testing class for university-scale validation"""
    
    def __init__(self, output_dir: Path = None):
        self.output_dir = output_dir or Path("stress_test_results")
        self.output_dir.mkdir(exist_ok=True)
        
        # Test files
        self.test_files = {
            "basic": project_root / "tests/data/university_scale_basic.lean",
            "intermediate": project_root / "tests/data/university_scale_intermediate.lean", 
            "advanced": project_root / "tests/data/university_scale_advanced.lean"
        }
        
        # Performance tracking
        self.metrics: List[PerformanceMetrics] = []
        self.process = psutil.Process()
        
        # Initialize components
        self.parser_config = ParserConfig()
        self.generator = OfflineGenerator()
        self.batch_exporter = BatchExporter()
        
    def measure_memory_usage(self) -> float:
        """Get current memory usage in MB"""
        return self.process.memory_info().rss / 1024 / 1024
    
    def measure_file_parsing_performance(self, file_path: Path) -> PerformanceMetrics:
        """Measure performance of parsing a single file"""
        logger.info(f"Testing file parsing performance: {file_path.name}")
        
        # Get file size
        file_size_mb = file_path.stat().st_size / 1024 / 1024
        baseline_memory = self.measure_memory_usage()
        
        # Parse the file
        parser = SimpleLeanParser()
        start_time = time.time()
        
        try:
            result = parser.parse_file(file_path)
            parse_time = time.time() - start_time
            
            theorems = result.theorems if result.success else []
            theorem_count = len(theorems)
            
            # Generate sketches for parsed theorems
            generation_start = time.time()
            successful_generations = 0
            generation_errors = []
            
            for theorem in theorems:
                try:
                    sketch = self.generator.generate_proof_sketch(theorem)
                    if sketch:
                        successful_generations += 1
                except Exception as e:
                    generation_errors.append(str(e))
            
            generation_time = time.time() - generation_start
            total_time = parse_time + generation_time
            peak_memory = self.measure_memory_usage()
            
            success_rate = successful_generations / max(theorem_count, 1)
            throughput = theorem_count / total_time if total_time > 0 else 0
            
            return PerformanceMetrics(
                operation=f"parse_file_{file_path.stem}",
                file_size_mb=file_size_mb,
                theorem_count=theorem_count,
                parse_time_seconds=parse_time,
                generation_time_seconds=generation_time,
                total_time_seconds=total_time,
                memory_peak_mb=peak_memory,
                memory_baseline_mb=baseline_memory,
                throughput_theorems_per_second=throughput,
                success_rate=success_rate,
                errors=generation_errors
            )
            
        except Exception as e:
            return PerformanceMetrics(
                operation=f"parse_file_{file_path.stem}_FAILED",
                file_size_mb=file_size_mb,
                theorem_count=0,
                parse_time_seconds=0,
                generation_time_seconds=0,
                total_time_seconds=time.time() - start_time,
                memory_peak_mb=self.measure_memory_usage(),
                memory_baseline_mb=baseline_memory,
                throughput_theorems_per_second=0,
                success_rate=0,
                errors=[str(e)]
            )
    
    def simulate_student_workload(self, student_id: int, files: List[Path]) -> List[PerformanceMetrics]:
        """Simulate a single student's workload"""
        logger.info(f"Student {student_id} starting workload simulation")
        student_metrics = []
        
        for file_path in files:
            try:
                metrics = self.measure_file_parsing_performance(file_path)
                metrics.operation = f"student_{student_id}_{metrics.operation}"
                student_metrics.append(metrics)
                
                # Simulate student thinking time
                time.sleep(0.1)
                
            except Exception as e:
                logger.error(f"Student {student_id} failed on {file_path}: {e}")
                
        logger.info(f"Student {student_id} completed workload")
        return student_metrics
    
    def test_concurrent_classroom_load(self, num_students: int = 25) -> Dict[str, Any]:
        """Test concurrent load from multiple students"""
        logger.info(f"Testing concurrent classroom load with {num_students} students")
        
        # Each student processes a subset of files
        student_files = [
            [self.test_files["basic"]],
            [self.test_files["intermediate"]], 
            [self.test_files["basic"], self.test_files["intermediate"]],
            [self.test_files["advanced"]]
        ]
        
        baseline_memory = self.measure_memory_usage()
        start_time = time.time()
        
        all_metrics = []
        failed_students = 0
        
        # Use ThreadPoolExecutor to simulate concurrent students
        with ThreadPoolExecutor(max_workers=min(num_students, 10)) as executor:
            # Submit student workloads
            futures = []
            for student_id in range(num_students):
                files = student_files[student_id % len(student_files)]
                future = executor.submit(self.simulate_student_workload, student_id, files)
                futures.append(future)
            
            # Collect results
            for future in as_completed(futures):
                try:
                    student_metrics = future.result(timeout=60)
                    all_metrics.extend(student_metrics)
                except Exception as e:
                    failed_students += 1
                    logger.error(f"Student workload failed: {e}")
        
        total_time = time.time() - start_time
        peak_memory = self.measure_memory_usage()
        
        # Analyze results
        successful_operations = [m for m in all_metrics if m.success_rate > 0]
        total_theorems = sum(m.theorem_count for m in all_metrics)
        avg_throughput = statistics.mean([m.throughput_theorems_per_second for m in successful_operations]) if successful_operations else 0
        
        return {
            "test_name": "concurrent_classroom_load",
            "num_students": num_students,
            "total_time_seconds": total_time,
            "memory_baseline_mb": baseline_memory,
            "memory_peak_mb": peak_memory,
            "memory_increase_mb": peak_memory - baseline_memory,
            "total_operations": len(all_metrics),
            "successful_operations": len(successful_operations),
            "failed_students": failed_students,
            "total_theorems_processed": total_theorems,
            "average_throughput_per_student": avg_throughput,
            "system_throughput_theorems_per_second": total_theorems / total_time if total_time > 0 else 0,
            "success_rate": len(successful_operations) / max(len(all_metrics), 1),
            "individual_metrics": [
                {
                    "operation": m.operation,
                    "theorem_count": m.theorem_count,
                    "total_time": m.total_time_seconds,
                    "success_rate": m.success_rate,
                    "throughput": m.throughput_theorems_per_second
                } for m in all_metrics
            ]
        }
    
    def test_large_file_scalability(self) -> Dict[str, Any]:
        """Test scalability with increasingly large files"""
        logger.info("Testing large file scalability")
        
        scalability_results = []
        
        for file_name, file_path in self.test_files.items():
            if not file_path.exists():
                logger.warning(f"Test file not found: {file_path}")
                continue
                
            logger.info(f"Testing scalability with {file_name} file")
            
            # Test the file multiple times to see consistency
            file_metrics = []
            for run in range(3):
                metrics = self.measure_file_parsing_performance(file_path)
                file_metrics.append(metrics)
            
            # Calculate statistics
            parse_times = [m.parse_time_seconds for m in file_metrics]
            total_times = [m.total_time_seconds for m in file_metrics]
            throughputs = [m.throughput_theorems_per_second for m in file_metrics]
            
            scalability_results.append({
                "file_type": file_name,
                "file_size_mb": file_metrics[0].file_size_mb,
                "theorem_count": file_metrics[0].theorem_count,
                "avg_parse_time": statistics.mean(parse_times),
                "std_parse_time": statistics.stdev(parse_times) if len(parse_times) > 1 else 0,
                "avg_total_time": statistics.mean(total_times),
                "std_total_time": statistics.stdev(total_times) if len(total_times) > 1 else 0,
                "avg_throughput": statistics.mean(throughputs),
                "std_throughput": statistics.stdev(throughputs) if len(throughputs) > 1 else 0,
                "consistency_score": 1.0 - (statistics.stdev(total_times) / statistics.mean(total_times)) if len(total_times) > 1 and statistics.mean(total_times) > 0 else 1.0,
                "runs": file_metrics
            })
        
        return {
            "test_name": "large_file_scalability",
            "files_tested": len(scalability_results),
            "results": scalability_results,
            "summary": {
                "max_file_size_mb": max(r["file_size_mb"] for r in scalability_results) if scalability_results else 0,
                "max_theorem_count": max(r["theorem_count"] for r in scalability_results) if scalability_results else 0,
                "avg_throughput_overall": statistics.mean([r["avg_throughput"] for r in scalability_results]) if scalability_results else 0,
                "min_consistency_score": min(r["consistency_score"] for r in scalability_results) if scalability_results else 0
            }
        }
    
    def test_memory_stress(self) -> Dict[str, Any]:
        """Test memory usage under stress conditions"""
        logger.info("Testing memory stress conditions")
        
        baseline_memory = self.measure_memory_usage()
        memory_samples = [baseline_memory]
        
        # Process all files simultaneously
        all_files = list(self.test_files.values())
        
        try:
            # Create multiple parser instances
            parsers = [SimpleLeanParser() for _ in range(5)]
            generators = [OfflineGenerator() for _ in range(3)]
            
            memory_samples.append(self.measure_memory_usage())
            
            # Parse all files with all parsers
            all_results = []
            for parser in parsers:
                for file_path in all_files:
                    if file_path.exists():
                        result = parser.parse_file(file_path)
                        all_results.append(result)
                        memory_samples.append(self.measure_memory_usage())
            
            # Generate sketches for all theorems
            for result in all_results:
                if result.success:
                    for theorem in result.theorems:
                        for generator in generators:
                            try:
                                generator.generate_proof_sketch(theorem)
                                memory_samples.append(self.measure_memory_usage())
                            except Exception:
                                pass
            
            peak_memory = max(memory_samples)
            memory_increase = peak_memory - baseline_memory
            
            return {
                "test_name": "memory_stress",
                "baseline_memory_mb": baseline_memory,
                "peak_memory_mb": peak_memory,
                "memory_increase_mb": memory_increase,
                "memory_samples": len(memory_samples),
                "memory_growth_rate": memory_increase / len(memory_samples) if memory_samples else 0,
                "operations_completed": len(all_results),
                "memory_efficiency": memory_increase / max(len(all_results), 1),
                "status": "PASSED" if memory_increase < 500 else "FAILED"  # 500MB threshold
            }
            
        except Exception as e:
            return {
                "test_name": "memory_stress",
                "error": str(e),
                "status": "ERROR"
            }
    
    def test_batch_processing_limits(self) -> Dict[str, Any]:
        """Test batch processing capabilities and limits"""
        logger.info("Testing batch processing limits")
        
        # Create multiple temporary theorem files
        batch_files = []
        temp_dir = tempfile.mkdtemp()
        
        try:
            # Create 20 small theorem files
            for i in range(20):
                theorem_file = Path(temp_dir) / f"theorem_{i}.lean"
                theorem_file.write_text(f"""
theorem test_theorem_{i} (n : ℕ) : n + 0 = n := by
  rfl

theorem test_theorem_{i}_comm (n m : ℕ) : n + m = m + n := by
  induction n with
  | zero => simp
  | succ n ih => simp [Nat.succ_add, Nat.add_succ, ih]

theorem test_theorem_{i}_assoc (a b c : ℕ) : (a + b) + c = a + (b + c) := by
  induction a with
  | zero => simp
  | succ a ih => simp [Nat.succ_add, ih]
""")
                batch_files.append(theorem_file)
            
            # Test batch processing
            start_time = time.time()
            baseline_memory = self.measure_memory_usage()
            
            # Use batch exporter  
            results = []
            memory_peak = baseline_memory
            
            # Process in batches - first parse all files
            all_theorems = []
            for file_path in batch_files:
                try:
                    parser = SimpleLeanParser()
                    result = parser.parse_file(file_path)
                    if result.success:
                        all_theorems.extend(result.theorems)
                except Exception as e:
                    logger.error(f"Failed to parse {file_path}: {e}")
            
            # Export using batch exporter
            try:
                export_result = self.batch_exporter.export_from_theorems(
                    all_theorems, 
                    self.generator,
                    formats=["markdown"],
                    create_index=True
                )
                results.append(export_result)
                current_memory = self.measure_memory_usage()
                memory_peak = max(memory_peak, current_memory)
            except Exception as e:
                logger.error(f"Batch export failed: {e}")
            
            total_time = time.time() - start_time
            
            return {
                "test_name": "batch_processing_limits",
                "files_processed": len(batch_files),
                "batches_completed": len(results),
                "total_time_seconds": total_time,
                "memory_baseline_mb": baseline_memory,
                "memory_peak_mb": memory_peak,
                "memory_increase_mb": memory_peak - baseline_memory,
                "throughput_files_per_second": len(batch_files) / total_time if total_time > 0 else 0,
                "batch_success_rate": len(results) / ((len(batch_files) + 4) // 5),  # Number of expected batches
                "status": "PASSED" if len(results) > 0 else "FAILED"
            }
            
        finally:
            # Cleanup
            import shutil
            shutil.rmtree(temp_dir, ignore_errors=True)
    
    def run_comprehensive_stress_test(self) -> Dict[str, Any]:
        """Run the complete stress test suite"""
        logger.info("Starting comprehensive university stress test")
        
        start_time = time.time()
        initial_memory = self.measure_memory_usage()
        
        # Collect system information
        system_info = {
            "cpu_count": multiprocessing.cpu_count(),
            "memory_total_gb": psutil.virtual_memory().total / (1024**3),
            "memory_available_gb": psutil.virtual_memory().available / (1024**3),
            "platform": sys.platform,
            "python_version": sys.version
        }
        
        test_results = {
            "test_suite": "university_stress_test",
            "timestamp": time.strftime("%Y-%m-%d %H:%M:%S"),
            "system_info": system_info,
            "initial_memory_mb": initial_memory
        }
        
        # Run individual tests
        tests = [
            ("single_file_performance", lambda: {f: self.measure_file_parsing_performance(p) for f, p in self.test_files.items() if p.exists()}),
            ("concurrent_classroom_small", lambda: self.test_concurrent_classroom_load(10)),
            ("concurrent_classroom_medium", lambda: self.test_concurrent_classroom_load(25)),
            ("concurrent_classroom_large", lambda: self.test_concurrent_classroom_load(50)),
            ("large_file_scalability", self.test_large_file_scalability),
            ("memory_stress", self.test_memory_stress),
            ("batch_processing", self.test_batch_processing_limits)
        ]
        
        for test_name, test_func in tests:
            logger.info(f"Running test: {test_name}")
            try:
                result = test_func()
                test_results[test_name] = result
                logger.info(f"Test {test_name} completed successfully")
            except Exception as e:
                logger.error(f"Test {test_name} failed: {e}")
                test_results[test_name] = {"error": str(e), "status": "FAILED"}
        
        # Calculate overall assessment
        test_results["overall_assessment"] = self.assess_university_readiness(test_results)
        test_results["total_test_time_seconds"] = time.time() - start_time
        test_results["final_memory_mb"] = self.measure_memory_usage()
        
        # Save results
        self.save_results(test_results)
        
        return test_results
    
    def assess_university_readiness(self, results: Dict[str, Any]) -> Dict[str, Any]:
        """Assess if the tool is ready for university-scale deployment"""
        
        assessment = {
            "production_ready": True,
            "university_scale": True,
            "classroom_ready": True,
            "concerns": [],
            "recommendations": [],
            "capacity_limits": {}
        }
        
        # Check single file performance
        if "single_file_performance" in results:
            perf_data = results["single_file_performance"]
            for file_type, metrics in perf_data.items():
                if hasattr(metrics, 'total_time_seconds') and metrics.total_time_seconds > 30:
                    assessment["concerns"].append(f"Slow processing for {file_type} files: {metrics.total_time_seconds:.1f}s")
                    assessment["production_ready"] = False
        
        # Check concurrent performance
        classroom_tests = ["concurrent_classroom_small", "concurrent_classroom_medium", "concurrent_classroom_large"]
        for test_name in classroom_tests:
            if test_name in results and "error" not in results[test_name]:
                test_result = results[test_name]
                if test_result.get("success_rate", 0) < 0.8:
                    assessment["concerns"].append(f"Low success rate in {test_name}: {test_result['success_rate']:.1%}")
                    assessment["classroom_ready"] = False
                
                if test_result.get("failed_students", 0) > test_result.get("num_students", 0) * 0.1:
                    assessment["concerns"].append(f"High failure rate in {test_name}: {test_result['failed_students']} failed students")
                    assessment["classroom_ready"] = False
        
        # Check memory usage
        if "memory_stress" in results and "error" not in results["memory_stress"]:
            memory_test = results["memory_stress"]
            if memory_test.get("memory_increase_mb", 0) > 1000:  # 1GB increase
                assessment["concerns"].append(f"High memory usage: {memory_test['memory_increase_mb']:.1f}MB increase")
                assessment["university_scale"] = False
        
        # Determine capacity limits
        if "concurrent_classroom_large" in results and "error" not in results["concurrent_classroom_large"]:
            large_test = results["concurrent_classroom_large"]
            if large_test.get("success_rate", 0) >= 0.8:
                assessment["capacity_limits"]["max_concurrent_students"] = 50
            elif "concurrent_classroom_medium" in results and results["concurrent_classroom_medium"].get("success_rate", 0) >= 0.8:
                assessment["capacity_limits"]["max_concurrent_students"] = 25
            else:
                assessment["capacity_limits"]["max_concurrent_students"] = 10
        
        # Overall grade
        concerns_count = len(assessment["concerns"])
        if concerns_count == 0:
            assessment["grade"] = "A - Excellent"
        elif concerns_count <= 2:
            assessment["grade"] = "B - Good with minor issues"
        elif concerns_count <= 4:
            assessment["grade"] = "C - Acceptable with concerns"
        else:
            assessment["grade"] = "F - Not ready for production"
        
        # Recommendations
        if not assessment["production_ready"]:
            assessment["recommendations"].append("Optimize file parsing performance before production deployment")
        if not assessment["classroom_ready"]:
            assessment["recommendations"].append("Improve concurrent processing reliability for classroom use")
        if not assessment["university_scale"]:
            assessment["recommendations"].append("Reduce memory footprint for large-scale deployments")
        
        return assessment
    
    def save_results(self, results: Dict[str, Any]):
        """Save test results to file"""
        timestamp = time.strftime("%Y%m%d_%H%M%S")
        results_file = self.output_dir / f"university_stress_test_{timestamp}.json"
        
        try:
            # Convert dataclasses to dicts for JSON serialization
            json_results = self.serialize_results(results)
            with open(results_file, "w") as f:
                json.dump(json_results, f, indent=2, default=str)
            logger.info(f"Results saved to: {results_file}")
        except Exception as e:
            logger.error(f"Failed to save results: {e}")
    
    def serialize_results(self, obj):
        """Convert complex objects to JSON-serializable format"""
        if isinstance(obj, dict):
            return {k: self.serialize_results(v) for k, v in obj.items()}
        elif isinstance(obj, list):
            return [self.serialize_results(item) for item in obj]
        elif isinstance(obj, PerformanceMetrics):
            return {
                "operation": obj.operation,
                "file_size_mb": obj.file_size_mb,
                "theorem_count": obj.theorem_count,
                "parse_time_seconds": obj.parse_time_seconds,
                "generation_time_seconds": obj.generation_time_seconds,
                "total_time_seconds": obj.total_time_seconds,
                "memory_peak_mb": obj.memory_peak_mb,
                "memory_baseline_mb": obj.memory_baseline_mb,
                "throughput_theorems_per_second": obj.throughput_theorems_per_second,
                "success_rate": obj.success_rate,
                "errors": obj.errors
            }
        else:
            return obj
    
    def print_summary_report(self, results: Dict[str, Any]):
        """Print a human-readable summary report"""
        print("\n" + "="*80)
        print("UNIVERSITY STRESS TEST REPORT")
        print("="*80)
        
        assessment = results.get("overall_assessment", {})
        
        print(f"\n📊 OVERALL GRADE: {assessment.get('grade', 'Unknown')}")
        print(f"🎯 Production Ready: {'✅ YES' if assessment.get('production_ready', False) else '❌ NO'}")
        print(f"🏫 University Scale: {'✅ YES' if assessment.get('university_scale', False) else '❌ NO'}")
        print(f"👥 Classroom Ready: {'✅ YES' if assessment.get('classroom_ready', False) else '❌ NO'}")
        
        if "capacity_limits" in assessment:
            limits = assessment["capacity_limits"]
            print(f"\n📈 CAPACITY LIMITS:")
            for limit_type, value in limits.items():
                print(f"   • {limit_type.replace('_', ' ').title()}: {value}")
        
        if assessment.get("concerns"):
            print(f"\n⚠️  CONCERNS ({len(assessment['concerns'])}):")
            for concern in assessment["concerns"]:
                print(f"   • {concern}")
        
        if assessment.get("recommendations"):
            print(f"\n💡 RECOMMENDATIONS:")
            for rec in assessment["recommendations"]:
                print(f"   • {rec}")
        
        # Performance summary
        if "concurrent_classroom_large" in results:
            classroom_data = results["concurrent_classroom_large"]
            print(f"\n🚀 PERFORMANCE HIGHLIGHTS:")
            print(f"   • Max Students Tested: {classroom_data.get('num_students', 'N/A')}")
            print(f"   • Success Rate: {classroom_data.get('success_rate', 0):.1%}")
            print(f"   • System Throughput: {classroom_data.get('system_throughput_theorems_per_second', 0):.2f} theorems/sec")
        
        print(f"\n⏱️  Total Test Time: {results.get('total_test_time_seconds', 0):.1f} seconds")
        print("="*80)

def main():
    """Main entry point for the stress test"""
    if len(sys.argv) > 1 and sys.argv[1] == "--help":
        print(__doc__)
        return
    
    # Create output directory
    output_dir = Path("university_stress_test_results")
    output_dir.mkdir(exist_ok=True)
    
    # Run stress test
    tester = UniversityStressTester(output_dir)
    
    print("🚀 Starting University-Scale Stress Test for Proof-Sketcher")
    print("This may take several minutes to complete...")
    
    try:
        results = tester.run_comprehensive_stress_test()
        tester.print_summary_report(results)
        
    except KeyboardInterrupt:
        print("\n❌ Test interrupted by user")
        sys.exit(1)
    except Exception as e:
        print(f"\n💥 Test failed with error: {e}")
        logger.exception("Stress test failed")
        sys.exit(1)

if __name__ == "__main__":
    main()