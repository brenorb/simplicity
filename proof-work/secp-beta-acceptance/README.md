# Multiplication and beta registration attempt

The candidate contains 351 entries: the existing 349, field multiplication,
and multiplication by beta. That number describes candidate metadata only.
No entries were promoted to the main registry by this attempt.

The unchanged normal command, `bash check-jets.sh --update-expected`, terminated
with exit status 1. The coverage fixtures and multiplication/beta source-review
gates passed, including 22 beta mutation tests. The next gate failed with
`Bitcoin base primitive name mismatch: LockTime`.
