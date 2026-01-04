#!/usr/bin/env python3
"""
WESH Validation Experiment on Rigetti Ankaa-3
Direct execution on AWS Braket quantum hardware
"""

import numpy as np
import pandas as pd
import json
from datetime import datetime
from braket.aws import AwsDevice, AwsQuantumTask
from braket.circuits import Circuit
from braket.devices import LocalSimulator
import time
import os

def create_wesh_circuit(N, theta_deg):
    """Create GHZ(theta) circuit for WESH testing"""
    circuit = Circuit()
    theta = np.deg2rad(theta_deg)
    
    # Prepare GHZ(theta) state
    circuit.ry(0, 2*theta)
    for i in range(1, N):
        circuit.cnot(0, i)
    
    # Three X toggles (simplified echo sequence)
    for _ in range(3):
        for i in range(N):
            circuit.x(i)
    
    # Measure in X basis
    for i in range(N):
        circuit.h(i)
    
    # Add explicit measurement
    circuit.measure_all()
    
    return circuit

def calculate_parity(counts):
    """Calculate parity from measurement counts"""
    parity = 0.0
    total = sum(counts.values())
    for bitstring, count in counts.items():
        ones = bitstring.count('1')
        sign = (-1)**ones
        parity += sign * count / total
    return parity

def main():
    """Execute WESH validation experiment on Rigetti Ankaa-3"""
    
    print("="*60)
    print("WESH VALIDATION ON RIGETTI ANKAA-3")
    print("="*60)
    
    # Configuration - matching Figure 4.9 parameters
    N_VALUES = [3, 4, 5, 6]
    THETA_VALUES = [25, 30, 35, 40, 45]
    SHOTS = 20000  # 20,000 shots per configuration as in Figure 4.9
    
    total_tasks = len(N_VALUES) * len(THETA_VALUES)
    cost_per_task = 0.30 + SHOTS * 0.0009
    total_cost = total_tasks * cost_per_task
    
    print(f"\nConfiguration:")
    print(f"  N values: {N_VALUES}")
    print(f"  Theta values: {THETA_VALUES} degrees")
    print(f"  Shots per configuration: {SHOTS:,}")
    print(f"  Total configurations: {total_tasks}")
    print(f"  Total shots: {total_tasks * SHOTS:,}")
    print(f"  Estimated cost: ${total_cost:.2f}")
    
    # Device check
    print("\nChecking device status...")
    device = AwsDevice("arn:aws:braket:us-west-1::device/qpu/rigetti/Ankaa-3")
    print(f"  Device: {device.name}")
    print(f"  Status: {device.status}")
    print(f"  Queue depth: {device.queue_depth().quantum_tasks} tasks")
    
    # Local test
    print("\nRunning local test...")
    sim = LocalSimulator()
    test_circuit = create_wesh_circuit(3, 30)
    test_result = sim.run(test_circuit, shots=100).result()
    print(f"  Test successful: {len(test_result.measurements)} measurements")
    
    # Confirmation
    confirm = input(f"\nProceed with {total_tasks} tasks for ${total_cost:.2f}? (type CONFIRM): ")
    
    if confirm != "CONFIRM":
        print("Aborted.")
        return
    
    # Submit tasks
    print("\nSubmitting tasks to Rigetti Ankaa-3...")
    tasks = []
    results_data = []
    
    for idx, N in enumerate(N_VALUES):
        for theta in THETA_VALUES:
            task_num = idx * len(THETA_VALUES) + THETA_VALUES.index(theta) + 1
            
            # Create and submit circuit
            circuit = create_wesh_circuit(N, theta)
            task = device.run(circuit, shots=SHOTS)
            
            # Store task info
            task_info = {
                'task_id': task.id,
                'N': N,
                'theta': theta,
                'shots': SHOTS,
                'status': 'submitted',
                'timestamp': datetime.now().isoformat()
            }
            tasks.append(task_info)
            
            print(f"  [{task_num:2d}/{total_tasks}] N={N}, theta={theta:2d} deg: {task.id}")
            
            # Small delay to avoid rate limits
            time.sleep(0.5)
    
    # Save task information
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    filename = f'rigetti_wesh_{timestamp}.json'
    
    metadata = {
        'experiment': 'WESH_Cross_Platform_Validation',
        'device': 'Rigetti_Ankaa-3',
        'timestamp': datetime.now().isoformat(),
        'configuration': {
            'N_values': N_VALUES,
            'theta_values': THETA_VALUES,
            'shots': SHOTS
        },
        'total_tasks': total_tasks,
        'total_cost': total_cost,
        'tasks': tasks
    }
    
    with open(filename, 'w') as f:
        json.dump(metadata, f, indent=2)
    
    print(f"\nSubmission complete!")
    print(f"  Tasks submitted: {len(tasks)}")
    print(f"  Metadata saved: {filename}")
    print(f"  Total cost: ${total_cost:.2f}")
    
    # Wait for results (optional)
    retrieve = input("\nRetrieve results now? (type YES or press Enter to skip): ")
    
    if retrieve == "YES":
        print("\nRetrieving results...")
        results = []
        
        for i, task_info in enumerate(tasks):
            task_id = task_info['task_id']
            # Use correct API: AwsQuantumTask
            task = AwsQuantumTask(arn=task_id)
            
            # Wait for completion
            while task.state() not in ['COMPLETED', 'FAILED', 'CANCELLED']:
                print(f"  Task {i+1}/{len(tasks)}: {task.state()}")
                time.sleep(5)
            
            if task.state() == 'COMPLETED':
                result = task.result()
                counts = result.measurement_counts
                parity = calculate_parity(counts)
                
                results.append({
                    'N': task_info['N'],
                    'theta': task_info['theta'],
                    'parity': parity,
                    'shots': SHOTS
                })
                print(f"  Task {i+1}: N={task_info['N']}, theta={task_info['theta']}, parity={parity:.4f}")
        
        # Save results
        results_df = pd.DataFrame(results)
        csv_filename = f'rigetti_results_{timestamp}.csv'
        results_df.to_csv(csv_filename, index=False)
        print(f"\nResults saved: {csv_filename}")
    
    print("\nExperiment complete.")

if __name__ == "__main__":
    main()
