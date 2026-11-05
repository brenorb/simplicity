# Superseded first full-run attempt

The first coordinator completed the baseline and CSFS child processes.
CSFS wrote 19 actual PASS results and a valid checkpoint. The coordinator
then stopped because Python's text line splitting treated embedded carriage
returns in BIP340 CSV comments as record boundaries. It never reported a
successful full cohort. The manifest and logs are unchanged.

The repaired checker uses actual LF record boundaries and matches each PASS
to its evaluation record. It counted two baseline and 19 CSFS results in
these exact logs, and returned zero for a cached-only log. Both checkpoints
were moved to an ignored archive. The replacement full cohort starts from
an empty checkpoint namespace and measures both programs again under the
same executable and source fingerprint.
