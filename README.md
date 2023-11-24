# SAT-Based Bounded Model Checking for Compositional Affine Hybrid Systems

To run unsafe instance and get counterexample, run (with a minimum bound and time horizon; may change the variable for CE plotting and the timestep):

`python3 nrs_unsafe.py 10 91 controller_x 0.1`

To run safe instance for a bound of 15, run:

`python3 nrs_safe.py 15 100 controller_x 0.1`
