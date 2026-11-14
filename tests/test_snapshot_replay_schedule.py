"""Exercise the shared replay bound, baseline serialization and failure path."""

from concurrent.futures import ThreadPoolExecutor
from threading import Event, Lock
import unittest

from reproduction.paper_results.check_snapshot_controls import ReplaySchedule


class ReplayScheduleTests(unittest.TestCase):
    def test_baseline_and_control_workers_share_two_slots_and_keep_result_order(self):
        entered = [Event() for _ in range(4)]
        release = Event()
        mutex = Lock()
        active = maximum = 0

        def replay(index):
            nonlocal active, maximum
            with mutex:
                active += 1
                maximum = max(maximum, active)
            entered[index].set()
            try:
                if not release.wait(5):
                    raise TimeoutError("test release missing")
                return {"name": str(index), "accepted": index == 0}
            finally:
                with mutex:
                    active -= 1

        results = [{"name": "earlier", "accepted": False}]
        try:
            with ReplaySchedule() as schedule, ThreadPoolExecutor(max_workers=3) as workers:
                schedule.baseline(results, replay, 0)
                self.assertTrue(entered[0].wait(5))
                futures = [workers.submit(schedule.execute, replay, i) for i in range(1, 4)]
                self.assertTrue(any(event.wait(0.1) for event in entered[1:]))
                self.assertEqual(sum(event.is_set() for event in entered), 2)
                self.assertIsNone(results[1])
                release.set()
                results.extend(f.result() for f in futures)
                schedule.resolve(results)
        finally:
            release.set()
        self.assertEqual(maximum, 2)
        self.assertEqual([row["name"] for row in results], ["earlier", "0", "1", "2", "3"])

    def test_baseline_reads_are_serial_even_when_one_shared_slot_is_free(self):
        first, second, release = Event(), Event(), Event()

        def baseline(index):
            (first if index == 1 else second).set()
            if index == 1 and not release.wait(5):
                raise TimeoutError("test release missing")
            return index

        try:
            with ReplaySchedule() as schedule:
                results = []
                schedule.baseline(results, baseline, 1)
                self.assertTrue(first.wait(5))
                schedule.baseline(results, baseline, 2)
                self.assertFalse(second.wait(0.1))
                self.assertEqual(schedule.execute(lambda: "independent control"), "independent control")
                release.set()
                schedule.resolve(results)
        finally:
            release.set()
        self.assertEqual(results, [1, 2])

    def test_baseline_failure_is_propagated_before_a_suite_can_report_success(self):
        def fail():
            raise RuntimeError("actual baseline failure")

        with ReplaySchedule() as schedule:
            results = [{"name": "earlier control", "accepted": False}]
            schedule.baseline(results, fail)
            results.append({"name": "later control", "accepted": False})
            with self.assertRaisesRegex(RuntimeError, "actual baseline failure"):
                schedule.resolve(results)
            self.assertIsNone(results[1])


if __name__ == "__main__":
    unittest.main()
