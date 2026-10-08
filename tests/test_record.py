import pytest

from jsp_records import CandidateRecord, RecordError, validate_record_payload
from jsp_records.record import default_erdos_90b_record


def test_default_record_contains_requested_claim_and_recipient():
    record = default_erdos_90b_record()
    assert record.record_id == "JSP-000106"
    assert record.recipient.name == "Shiqiang Chen"
    assert record.verification.commit == "1268917de"
    assert record.verification.file_count == 32
    assert "Real.log" in record.formal_statement


def test_json_round_trip_is_lossless():
    record = default_erdos_90b_record()
    assert CandidateRecord.from_dict(record.to_dict()) == record
    assert CandidateRecord.from_dict(__import__("json").loads(record.to_json())) == record


@pytest.mark.parametrize("field,value", [("record_id", "bad"), ("problem_url", "http://www.erdosproblems.com/90")])
def test_rejects_invalid_identity_or_url(field, value):
    record = default_erdos_90b_record().to_dict()
    record[field] = value
    with pytest.raises(RecordError):
        CandidateRecord.from_dict(record)


def test_rejects_bad_commit_and_negative_counts():
    record = default_erdos_90b_record().to_dict()
    record["verification"]["commit"] = "not-a-sha"
    with pytest.raises(RecordError):
        CandidateRecord.from_dict(record)
    record = default_erdos_90b_record().to_dict()
    record["verification"]["patch_count"] = -1
    with pytest.raises(RecordError):
        CandidateRecord.from_dict(record)


def test_rejects_secret_like_payload():
    record = default_erdos_90b_record().to_dict()
    record["result_summary"] = "token=should-not-be-stored"
    with pytest.raises(RecordError):
        CandidateRecord.from_dict(record)


@pytest.mark.parametrize("url", [
    "https://www.erdosproblems.com/90?raw=1",
    "https://www.erdosproblems.com/90#part-b",
    "http://www.erdosproblems.com/90",
    "https://evil.example/90",
])
def test_rejects_noncanonical_problem_urls(url):
    payload = default_erdos_90b_record().to_dict()
    payload["problem_url"] = url
    with pytest.raises(RecordError):
        validate_record_payload(payload)


def test_rejects_non_mapping_payloads():
    with pytest.raises(RecordError, match="mapping"):
        CandidateRecord.from_dict(None)


def test_rejects_empty_axiom_and_non_integer_counts():
    payload = default_erdos_90b_record().to_dict()
    payload["verification"]["axioms"] = ["propext", ""]
    with pytest.raises(RecordError):
        validate_record_payload(payload)

    payload = default_erdos_90b_record().to_dict()
    payload["verification"]["file_count"] = "32"
    with pytest.raises(RecordError):
        validate_record_payload(payload)
