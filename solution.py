"""Entry points for the JSP-000106 candidate-record workflow."""

from collections.abc import Mapping

from jsp_records import CandidateRecord, RecordError, default_erdos_90b_record, validate_record_payload


TASK_NAME = "JSP-000106 [Recipient]: Shiqiang Chen — Erdős problem 90(b) verification credit"


def build_record(data: Mapping | None = None) -> CandidateRecord:
    """Return the canonical record, or validate a supplied serialized payload."""

    if data is None:
        return default_erdos_90b_record()
    return validate_record_payload(data)

def solve_task(data: dict) -> dict:
    """Validate a record payload while retaining the original task API."""
    if not isinstance(data, dict):
        raise ValueError("Invalid input format")
    # Generic input remains supported for callers of the original scaffold;
    # a record-shaped payload is validated rather than merely echoed.
    record = None
    if "record_id" in data:
        try:
            record = build_record(data)
        except RecordError as exc:
            raise ValueError(str(exc)) from exc
    return {
        "status": "success",
        "task": TASK_NAME,
        "processed": True,
        "data": data,
        **({"record": record.to_dict()} if record is not None else {}),
    }
