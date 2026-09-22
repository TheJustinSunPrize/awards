"""The immutable, serializable representation of a verified-pending record."""

from __future__ import annotations

from dataclasses import asdict, dataclass
import json
import re
from typing import Any, Mapping
from urllib.parse import urlparse


class RecordError(ValueError):
    """Raised when a record is incomplete or contains invalid provenance."""


_SHA = re.compile(r"^[0-9a-f]{7,40}$")
_SECRET = re.compile(r"(?i)(api[_-]?key|token|secret|password|private[_-]?key)\s*[:=]")


def _https_url(value: str, *, host: str | None = None) -> str:
    parsed = urlparse(value)
    if parsed.scheme != "https" or not parsed.netloc or parsed.query or parsed.fragment:
        raise RecordError("URLs must be absolute HTTPS URLs without query or fragment")
    if host and parsed.hostname != host:
        raise RecordError(f"URL must use {host}")
    return value


@dataclass(frozen=True)
class Recipient:
    name: str
    name_zh: str
    github_url: str

    def __post_init__(self) -> None:
        if not self.name.strip() or not self.name_zh.strip():
            raise RecordError("recipient names are required")
        _https_url(self.github_url, host="github.com")


@dataclass(frozen=True)
class Verification:
    repository: str
    commit: str
    file_count: int
    lean_version: str
    mathlib_version: str
    patch_count: int
    axioms: tuple[str, ...]

    def __post_init__(self) -> None:
        if not self.repository or "/" not in self.repository:
            raise RecordError("repository must be in owner/name form")
        if not _SHA.fullmatch(self.commit):
            raise RecordError("commit must be a lowercase Git SHA (7 to 40 characters)")
        if self.file_count < 1 or self.patch_count < 0:
            raise RecordError("file_count must be positive and patch_count non-negative")
        if not self.lean_version or not self.mathlib_version:
            raise RecordError("compiler and mathlib versions are required")
        if not self.axioms or any(not axiom.strip() for axiom in self.axioms):
            raise RecordError("at least one non-empty axiom is required")


@dataclass(frozen=True)
class CandidateRecord:
    record_id: str
    problem_title: str
    problem_url: str
    result_summary: str
    formal_statement: str
    theorem_name: str
    verification: Verification
    recipient: Recipient
    credit_type: str = "verification_only"
    status: str = "verified_pending"

    def __post_init__(self) -> None:
        if not re.fullmatch(r"JSP-\d{6}", self.record_id):
            raise RecordError("record_id must match JSP-######")
        if not self.problem_title.strip() or not self.result_summary.strip():
            raise RecordError("problem title and result summary are required")
        _https_url(self.problem_url, host="www.erdosproblems.com")
        if not self.formal_statement.strip() or not self.theorem_name.strip():
            raise RecordError("formal statement and theorem name are required")
        if self.credit_type != "verification_only":
            raise RecordError("credit_type must be verification_only")
        if self.status not in {"verified_pending", "verified", "rejected"}:
            raise RecordError("unsupported record status")
        payload = json.dumps(asdict(self), ensure_ascii=False)
        if _SECRET.search(payload):
            raise RecordError("record contains a secret-like field")

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)

    def to_json(self) -> str:
        return json.dumps(self.to_dict(), ensure_ascii=False, sort_keys=True, indent=2) + "\n"

    @classmethod
    def from_dict(cls, data: Mapping[str, Any]) -> "CandidateRecord":
        if not isinstance(data, Mapping):
            raise RecordError("record payload must be a mapping")
        try:
            verification_data = dict(data["verification"])
            recipient_data = dict(data["recipient"])
            verification_data["axioms"] = tuple(verification_data["axioms"])
            return cls(
                **{k: v for k, v in data.items() if k not in {"verification", "recipient"}},
                verification=Verification(**verification_data),
                recipient=Recipient(**recipient_data),
            )
        except (AttributeError, KeyError, TypeError, ValueError) as exc:
            if isinstance(exc, RecordError):
                raise
            raise RecordError(f"invalid record payload: {exc}") from exc


def default_erdos_90b_record() -> CandidateRecord:
    return CandidateRecord(
        record_id="JSP-000106",
        problem_title="Erdős problem 90(b) — unit distances in the plane",
        problem_url="https://www.erdosproblems.com/90",
        result_summary="The proposed uniform bound is false for every absolute constant C.",
        formal_statement="∀ C : ℝ, 0 < C → ∀ N : ℕ, ∃ (n : ℕ) (P : Finset Point), N ≤ n ∧ P.card = n ∧ (n : ℝ) ^ (1 + C / Real.log (Real.log n)) < (unitDistancePairs P : ℝ)",
        theorem_name="Erdos90b.not_erdos_90 (alias Erdos90b.erdos_90b)",
        verification=Verification("plby/lean-proofs", "1268917de", 32, "4.34.0", "4.34.0", 8, ("propext", "Classical.choice", "Quot.sound")),
        recipient=Recipient("Shiqiang Chen", "陈世强", "https://github.com/shunfeng8421"),
    )


def validate_record_payload(data: Mapping[str, Any]) -> CandidateRecord:
    """Parse and validate an externally supplied candidate-record payload."""

    return CandidateRecord.from_dict(data)
