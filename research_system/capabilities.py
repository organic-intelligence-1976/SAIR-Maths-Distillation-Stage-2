"""Capability manifests, masks, and intervention-boundary audits."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Callable

import baby_solver


@dataclass(frozen=True)
class CapabilityMask:
    disabled: tuple[str, ...] = ()

    @classmethod
    def from_value(cls, value: Any = None) -> "CapabilityMask":
        normalized = baby_solver.normalize_capability_mask(value)
        return cls(tuple(normalized["disabled"]))

    def to_mapping(self) -> dict[str, list[str]]:
        return {"disabled": list(self.disabled)}


class CapabilityService:
    def manifest(self, mask: CapabilityMask | Any = None) -> dict[str, Any]:
        value = mask.to_mapping() if isinstance(mask, CapabilityMask) else mask
        return baby_solver.capability_manifest(value)

    def gate(self, tool: str, mask: CapabilityMask | Any = None) -> dict[str, Any] | None:
        value = mask.to_mapping() if isinstance(mask, CapabilityMask) else mask
        return baby_solver.capability_gate_state(tool, value)

    def audit_intervention(
        self,
        *,
        full_run: Callable[[], tuple[bool, dict[str, Any]]],
        withheld_run: Callable[[], tuple[bool, dict[str, Any]]],
        generic_run: Callable[[], tuple[bool, dict[str, Any]]],
        negative_run: Callable[[], tuple[bool, dict[str, Any]]],
    ) -> dict[str, Any]:
        full_ok, full_state = full_run()
        withheld_ok, withheld_state = withheld_run()
        generic_ok, generic_state = generic_run()
        negative_ok, negative_state = negative_run()
        checks = {
            "full_capability_succeeds": full_ok,
            "shortcut_is_withheld": (
                not withheld_ok and withheld_state.get("status") == "withheld_for_curriculum"
            ),
            "generic_recovery_succeeds": generic_ok,
            "negative_control_removes_recovery": not negative_ok,
            "generic_did_not_use_masked_fallback": not str(
                generic_state.get("status") or ""
            ).startswith("body_built_by_focused_"),
        }
        return {
            "eligible": all(checks.values()),
            "checks": checks,
            "states": {
                "full": full_state,
                "withheld": withheld_state,
                "generic": generic_state,
                "negative": negative_state,
            },
        }
