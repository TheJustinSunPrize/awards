"""Unit tests for automated solution."""
import pytest
from solution import build_record, solve_task

def test_solve_task_success():
    res = solve_task({"key": "value"})
    assert res["status"] == "success"
    assert res["processed"] is True

def test_solve_task_invalid():
    with pytest.raises(ValueError):
        solve_task("invalid")


def test_build_record_defaults_to_requested_candidate():
    assert build_record().record_id == "JSP-000106"


def test_solve_task_validates_record_payload():
    payload = build_record().to_dict()
    result = solve_task(payload)
    assert result["record"]["status"] == "verified_pending"


def test_solve_task_rejects_invalid_record_payload():
    payload = build_record().to_dict()
    payload["recipient"]["github_url"] = "http://github.com/shunfeng8421"
    with pytest.raises(ValueError):
        solve_task(payload)
