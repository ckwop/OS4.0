# Release 1.0 plan

**Target:** 2026-12-01. The MUD, with combat, served from a Graviton EC2 instance (t4g), booted from our own AMI, with player data on a separate EBS volume. Decided 2026-11-12 (DECISIONS.md #151-155).

**Status:** planning. No release work has started.

## What "done" means

- Milestone 12's acceptance test passes: the AMI boots on a t4g instance and serves the MUD from a separate EBS data volume.
- MUD phase 2B (combat) is done in `os4-mud`, built contract first: each word's contract is written and read against the code before it is tested, then hostile tests, then proofs.
- No open `docs/tech-debt.md` entry is marked **must fix before public**.
- The release gate (below) passes on the release commit.

## Decisions

| # | Decision |
| --- | --- |
| 151 | Skip milestone 11 (Fargate); go straight to EC2. If the ENA driver slips, the date slips. |
| 152 | Agents run the AWS CLI under a profile the user logs in to: one region, t4g only, everything tagged `os4`, instances terminated after each session. The user keeps a billing alarm. |
| 153 | TD-36: reset a device after a timed-out request (the full fix). |
| 154 | TD-42: one failed-login budget shared by every login, plus a delay after each wrong password. |
| 155 | The user area grows from 512 to 1024 bytes per task. |

## Workstreams

### A. EC2 platform (milestone 12, this repository)

| Work | Tested in | Risk |
| --- | --- | --- |
| Raw boot image to S3, `import-snapshot`, `register-image` (UEFI, `--ena-support`); a first boot that prints on the EC2 serial console | AWS | Low. Do it first: it proves Limine and UEFI on Graviton |
| ACPI tables: SPCR for the UART, MCFG for PCIe; PCIe enumeration | QEMU | Medium |
| NVMe driver behind the block HAL; sector size; the data volume found by its header and its EBS volume ID (NVMe serial) | QEMU (`-device nvme`), then EBS | Medium |
| ENA driver behind the network HAL | A real instance only, over the serial console | **High**: QEMU cannot emulate it |
| DHCP client (TD-18) | QEMU user networking | Low |
| Entropy without virtio-rng (TD-24): `RNDR` if the CPU has it (Graviton2 probably does not), else timer jitter | QEMU, then t4g | Medium |
| Device reset after a timeout (TD-36, #153), for virtio, NVMe and ENA | QEMU | Medium |

### B. Combat (MUD phase 2B, `os4-mud`)

The brief is `os4-mud/docs/combat-brief.md`; its five open questions are settled in a separate session before combat starts. The base work combat needs comes first: the larger user area (#155).

### C. Bugs and proofs (this repository)

- Have `tools/forth2lean.py` generate the memory offsets the hand proofs use (user variables, reserved buffers), so a layout change no longer breaks them by hand.
- TD-42's shared login budget (#154).
- Finish V4: the connection-lookup chain through open and free, the loops listed in `proofs/yields.txt`, the virtio queue setup (H-queue).
- Hunt runs over each new driver as it lands, contract first: everything a device may send is hostile.
- A security review of what is reachable from the internet; it marks anything else that must be fixed before public.

## Timeline

| Dates | Base (A, C) | MUD (B) |
| --- | --- | --- |
| 12-15 Nov | AMI pipeline and a serial "hello" on t4g; generated proof offsets; user area 1024 | Settle the brief's questions; write the contracts |
| 16-21 Nov | ACPI, PCIe, NVMe, DHCP, entropy, device reset (QEMU); TD-42 | Combat code against the contracts; hostile `players` tests |
| 22-27 Nov | ENA on a real instance; NVMe on EBS; the MUD on EC2 end to end | Combat proofs; balance |
| 28 Nov | Freeze | Freeze |
| 28-30 Nov | Release gate | Release gate |
| 1 Dec | Launch | |

Docker runs one proof build at a time (5 GB VM), so the two streams take turns with it; work on real instances needs no Docker.

## Release gate

1. A full re-prove of both repositories from clean (`make proofs`), and the full `make test` in each.
2. Soak and hostile runs (`soak`, `hostile`, `tcp-attack`, `players`) against the real instance, not only QEMU.
3. The security review's findings fixed or accepted; no **must fix before public** entry open.
4. A reboot test on EC2: player data survives a stop and start, and an AMI swap with the data volume reattached.
5. Tag the release, and the `os4` image the MUD builds against.

## Risks

- **ENA** can only be debugged on real hardware. Each cycle is an image upload, an import and a boot (perhaps 15-30 minutes). Start it by 22 Nov at the latest.
- **Entropy:** without `RNDR`, timer jitter must be good enough to seed `random`; review it before launch.
- **Graviton firmware:** UEFI and ACPI on EC2 may differ from QEMU's in ways only a real boot shows. The first-week serial "hello" is there to find out early.
- **Docker** is one shared 5 GB VM: long proof builds on both streams compete for it.
