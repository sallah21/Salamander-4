# ModelSim Command Script to run the testbench

# Create a new project
vlib work
vmap work work

# Compile the design and testbench
 vlog -sv top_level.sv ./verif/TB.sv

# Start the simulation
vsim work.TB

# Run the simulation for a specified time (e.g., 1000 ns)
run 1000 ns

# Exit the simulation
quit
