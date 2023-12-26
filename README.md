# SAT-Based Bounded Model Checking for Compositional Affine Hybrid Systems

To run unsafe instance of NRS 5 and get counterexample, run (with a minimum bound and time horizon; may change the variable for CE plotting):

`python3 main.py nrs_5_unsafe 10 91 controller_x`

![NRS 5 counterexample](img/Figure_1.png)

To run safe instance of NRS 5 for a bound of 15, run:

`python3 main.py nrs_5_safe 15 100 controller_x`

To run safe instance of Tank-Burner-Thermometer for a bound of 15, run:

`python3 main.py tank 15 100 x`
