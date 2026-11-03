#!/usr/bin/env python3
"""Mock enrichment backend for tests: no network, no LLM.

Contract (documented in src/enrich.rs): the backend receives the full prompt
as its final argument; the prompt ends with a line "EVIDENCE:" followed by the
evidence-pack JSON array. This mock parses that array and names every cluster
mechanically (MockCluster0, MockCluster1, ...), proving the enrich loop
end-to-end while staying fully deterministic and offline.
"""
import json
import sys

prompt = sys.argv[-1]
marker = "EVIDENCE:\n"
start = prompt.index(marker) + len(marker)
evidence = json.loads(prompt[start:])
reply = [
    {
        "cluster_id": cluster["cluster_id"],
        "name": f"MockCluster{i}",
        "description": "A mock-named cluster used by the offline test backend.",
        "responsibilities": ["mock naming", "offline testing", "loop verification"],
    }
    for i, cluster in enumerate(evidence)
]
print(json.dumps(reply))
