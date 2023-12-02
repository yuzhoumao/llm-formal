import os
import subprocess

FILE_TO_RUN = {
    'CheckpointCoordination': 'MCCheckpointCoordination.tla',
    'CoffeeCan': 'CoffeeCan.tla',
    'DieHard': 'DieHard.tla',
    'DiningPhilosophers': 'DiningPhilosophers.tla',
    'Echo': 'MCEcho.tla',
    'FastPaxos': 'FastPaxos.tla',
    'FindHighest': 'MCFindHighest.tla',
    'KVStoreSnapshotIsolation': 'MCKVStoreSnapshotIsolation.tla',
    'LeastCircularSubstring': 'MCLeastCircularSubstring.tla',
    'Majority': 'MCMajority.tla',
    'Paxos': 'MCPaxos.tla',
    'Prisoners': 'MCPrisoners.tla',
    'ReadersWriters': 'MCReadersWriters.tla',
    'RingLeader': 'RingLeader.tla',
    'SchedulingAllocator': 'SchedulingAllocator.tla',
    'SimpleAllocator': 'SimpleAllocator.tla',
    'SingleLaneBridge': 'MCSingleLaneBridge.tla',
    'SlidingPuzzles': 'SlidingPuzzles.tla'
}


def main():
    parent_dir = os.path.dirname(os.path.abspath(__file__))
    input_dir = os.path.join(parent_dir, 'input')
    output_dir = os.path.join(parent_dir, 'model-outputs/gpt4/code/')
    lib_dir = os.path.join(parent_dir, 'lib')

    for protocol_filename in os.listdir(output_dir):
        protocol_name = protocol_filename.split('.tla')[0]
        print(protocol_name)
        
        output_filename = os.path.join(output_dir, protocol_name + '.tla')
        protocol_dir = os.path.join(input_dir, protocol_name)
        
        for lib_file in os.listdir(lib_dir):
            subprocess.run(['cp', '-r', os.path.join(lib_dir, lib_file), protocol_dir], check=True, text=True)
        
        input_filename = os.path.join(protocol_dir, protocol_name + '.tla')
        
        print(output_filename, input_filename)
        
        subprocess.run(['cp', output_filename, input_filename], check=True, text=True)
        output = subprocess.run(['java', \
                                    '-cp', \
                                    './tla2tools.jar', \
                                    'tlc2.TLC', \
                                    '-deadlock', \
                                    '-workers', '4', \
                                    os.path.join(protocol_dir, FILE_TO_RUN[protocol_name])], \
                                    check=False)
        stdout, stderr = output.stdout, output.stderr
        print(stdout, stderr)

            
    
if __name__ == '__main__':
    main()