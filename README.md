# GoPro MAX & HERO/Mission 1 Mapillary and Google Street View Workflow Tool

GoPro Workflow is a comprehensive Windows desktop application written in Python for processing footage from the **GoPro MAX 1**, **GoPro MAX 2**, **GoPro HERO series**, and **GoPro Mission 1 series** for use with **Mapillary** and **Google Street View**.

The application automates video preparation, GPMF metadata extraction and muxing, GPX generation, GPS validation and recovery, optional Nadir processing, frame sampling, Mapillary processing and upload, Street View MP4/GPX preparation, and optional Google Street View upload and status tracking.

> [!IMPORTANT]
> Use the latest available release. GoPro Workflow includes an automatic version checker, but development and beta builds may contain newer fixes than older public releases.

## Support the project

If GoPro Workflow saves time and you would like to support development:

[Buy me a coffee via PayPal](https://www.paypal.com/paypalme/mfaken)

## Privacy and Google authorization

- [GoPro Workflow homepage](https://gopro-workflow.faken.eu/)
- [Privacy Policy](https://gopro-workflow.faken.eu/privacy.html)

Google authorization is optional and is used only for Google Street View upload and status retrieval. GoPro Workflow never receives or stores a Google password. Google sign-in takes place in the normal system browser.

The distributed Windows application uses a bundled production Desktop OAuth client. A local authorization token is stored so that a valid session can be restored without opening the browser at every startup. Access can be removed with **Sign out** in GoPro Workflow or revoked in the Google Account security settings.

The OAuth application is intended for a limited group of known users and is not independently verified by Google. Google may therefore show an **unverified app** warning during first authorization.

## Core principles

- GoPro Workflow maintains one central, validated GPS and timestamp authority.
- Mapillary and Google Street View consume the same validated route and timeline.
- Neither Mapillary nor Google Street View is authoritative for the other.
- GPS recovery is fail-safe and auditable.
- The workflow does not invent GPS positions or timestamps.
- Unsafe outputs are blocked instead of silently accepted.

## Features

### Graphical user interface

- Windows GUI built with Tkinter.
- Separate workflows for GoPro MAX and HERO/Mission 1 footage.
- Configuration for source and target locations, video quality, GPU encoding, Nadir processing, Mapillary and Google Street View.
- Standard and Extended Output Logs, including TXT and XML output.
- Detailed per-file workflow monitoring.
- Per-phase progress, queue and upload tracking.
- GPS route preview and expandable GPS Vector Editor.
- Clear final accepted, rejected and failed summaries.
- Persistent JSON settings with safe migration.
- Early startup splash during the packaged one-file executable bootstrap.

### Current bundled toolchain

The packaged release is designed around:

- **FFmpeg 9.1** and matching FFprobe as the automatic default.
- Optional manual FFmpeg 9.0.1, 8.1.2 and 8.1.1 selections.
- Automatic FFmpeg 8.1.1 NVENC compatibility fallback for older NVIDIA drivers where applicable.
- **ExifTool 13.64**.
- **Mapillary Tools 0.15.1**.
- Portable ImageMagick for the restricted PNG-only Nadir workflow.

A manually selected FFmpeg version remains active until **Automatic (FFmpeg 9.1)** is selected again.

## GoPro MAX 360-degree workflow

### Camera support

- GoPro MAX 1, including 2019 and 2025 models.
- GoPro MAX 2.

### Video-mode support

- Standard video.
- TimeWarp 2X.
- TimeWarp 5X.
- Automatic MAX-family and recording-mode detection.

Other TimeWarp factors are intentionally rejected because they are not validated for the complete Mapillary and Street View workflow.

### Supported stitched video formats

- GoPro CineForm.
- HEVC/H.265.
- H.264.

### Automated preparation

- Matching of original `.360` files and stitched `.mp4` or `.mov` exports.
- GPMF stream detection and extraction.
- MAX 2 legacy GPMF stream compatibility.
- GPMF metadata muxing into prepared media.
- Metadata transfer from the original `.360` file.
- Video-stream validation with FFprobe.
- 8-bit and 10-bit handling.
- Preservation of equirectangular projection metadata where supported.
- Codec-aware heavy-processing capacity for CineForm and HEVC.

## Essential GoPro Player export settings

For MAX footage, export a stitched equirectangular video with the highest available resolution.

Recommended settings include:

- Use **Batch Exporter** where appropriate.
- Enable **Horizon Level**.
- Keep **Horizon Lock enabled for all supported use cases**, including walking, cycling and driving, for both Mapillary and Google Street View.
- Select HEVC for compact output or CineForm when maximum intermediate quality is required.
- Use the highest available export quality.

The original `.360` recording and stitched video must use the same base name.

Example:

```text
GS010123.360
GS010123.mp4
```

or:

```text
GS010123.360
GS010123.mov
```

## Early GPS preflight

GPS is checked immediately after the GPMF stream is available and before expensive video processing begins.

The preflight can detect:

- Missing GPS data.
- Missing, empty or invalid timestamps.
- Duplicate timestamps.
- Locally backward or non-monotonic timestamps.
- Invalid coordinates.
- Startup points without a valid fix.
- Unrealistic speed discontinuities.
- Isolated GPS jumps.
- Displaced GPS clusters.
- GPS continuity gaps.
- Insufficient timed anchors.
- TimeWarp timeline inconsistencies.

When a route cannot be recovered safely and is not required by another enabled output, GoPro Workflow skips unnecessary heavy processing such as Nadir encoding, muxing, metadata transfer, GPX generation and Street View timestamp correction.

## GPS normalization and recovery

The GPS engine uses original coordinates and timestamps from the GoPro telemetry.

> [!IMPORTANT]
> GoPro Workflow does not generate synthetic GPS positions or timestamps.

Supported operations include:

- Removal of coordinate samples without usable timestamps.
- Exclusion of invalid startup points such as `fix=0`, invalid DOP or `0,0` coordinates.
- Recovery of duplicate timestamps.
- Removal of limited locally backward timestamps.
- Correction of isolated speed jumps.
- Recovery of short displaced point sequences.
- Iterative multi-point cluster recovery.
- Removal of a safely identifiable faulty final GPS tail.
- Complete validation after every accepted correction.

After every accepted correction, the active route is rebuilt and all distances, speeds, courses and acceleration transitions are recalculated.

## Iterative GPS recovery

Difficult routes are processed iteratively:

1. Detect the worst remaining discontinuity.
2. Test multiple point-removal windows.
3. Evaluate each possible replacement bridge.
4. Apply only a safe candidate.
5. Rebuild the complete active route.
6. Recalculate geometry and speed statistics.
7. Search for the next discontinuity.
8. Continue until stable or no safe recovery remains.
9. Run complete post-recovery validation.

### Recovery limits

- Maximum of 12 points per local candidate.
- Maximum of 30 removed timed points per complete route.
- Maximum of 10 recovery rounds.
- Maximum bridge duration of 10 seconds.
- No coordinate interpolation.
- No timestamp interpolation.
- No point reordering.
- Complete final-route validation.

If no safe recovery is possible, the item is rejected and transferred to the run-specific `Needs_Review` structure with a machine-readable reason.

## Movement-profile detection

Routes are automatically classified from robust speed distributions and route characteristics rather than one maximum-speed value.

Supported profiles:

- `walking`
- `cycling`
- `urban_fast`
- `driving`

The analysis includes average speed, median, P75, P90, P95, proportions of faster segments, local medians and route geometry.

### Dynamic correction limits

| Profile | Dynamic correction range |
| --- | ---: |
| Walking | Conservative, normally around 30 km/h |
| Cycling | 65–90 km/h |
| Urban fast | 80–120 km/h |
| Driving | 150–250 km/h |

A point is never removed solely because a calculated speed exceeds the active limit. The surrounding geometry, course, distance, duration and replacement bridge are also evaluated.

### Advanced checks

- Bridge distance and duration.
- Bridge speed.
- Local median speed.
- Incoming and outgoing speeds.
- Incoming and outgoing course.
- Course change across the bridge.
- Acceleration around the transition.
- Distance to the expected route corridor.
- Remaining issues after rebuilding.
- Compact-route and intentional-turnaround analysis.

## GPS review

Routes requiring user review can be opened in the GPS Vector Editor. Available map layers include streets, cycling and satellite imagery.

The review workflow supports:

- Route inspection at detailed zoom levels.
- Safe removal of selected points.
- Revalidation after edits.
- Acceptance of legitimate speed-warning situations without deleting route points.
- Explicit rejection.
- Audit logging of decisions.

A successful final validation replaces a provisional early-review state. Downstream processing remains blocked until the route is definitively accepted or rejected.

## Mapillary integration

- Mapillary Tools 0.15.1 is the leading runtime.
- The workflow performs its own central GPX and timestamp validation before Mapillary processing.
- Supported actions:
  - Sample, Process and Upload.
  - Sample and Process Only.
  - Upload Only.
- Dynamic FIFO queues for sampling and upload.
- Mapillary uploads do not consume heavy sampling capacity.
- Existing upload history and already-uploaded content are classified separately from failures.
- Mapillary output is parsed independently of timestamped log prefixes.
- Upload success, duplicates, processing status and cleanup status remain separate data.

### Sample-range protection

Before a full-route GPS override is applied, the workflow compares the Mapillary sample time range with the video duration.

A clearly truncated sample range is blocked instead of being stretched over the complete GPX route. Distributed authority anchors are checked at approximately:

```text
0%, 10%, 25%, 50%, 75%, 90%, 100%
```

## Google Street View preparation

- GPX generation from validated GoPro telemetry.
- Creation of compatible MP4/GPX pairs.
- QuickTime header synchronization with the first valid GPX timestamp.
- Validation of critical QuickTime date fields.
- Separate routes for MAX 1 Standard, MAX 2 Standard and supported TimeWarp footage.
- Optional removal of audio from the prepared Street View video.
- Fail-safe rejection when a valid pair cannot be produced.

### Synchronized QuickTime fields

- Create Date.
- Modify Date.
- Track Create Date.
- Track Modify Date.
- Media Create Date.
- Media Modify Date.

## Google Street View upload

Google Street View upload is optional and uses the Google Street View Publish API internally.

- Bundled production Desktop OAuth client.
- Sign-in through the normal system browser.
- PKCE, state validation and a localhost callback.
- No Google password is received or stored by GoPro Workflow.
- Silent refresh-token restoration at startup.
- Interactive login only after the user selects **Sign in with Google**.
- Color-coded authorization status in Configuration and Street View Uploads.
- Exactly one active Street View upload at a time.
- Safe serial FIFO upload queue.
- Local tracking of operation and PhotoSequence identifiers.
- Direct links to the exact sequence in Street View Studio.
- Manual linking of existing Street View Studio uploads.
- Status-aware archive and recovery actions.
- Explicit sign-out and local credential removal.

### Google processing status

- For the first 60 days, a non-terminal Google record remains in the normal **Processing** view.
- From day 60 onward, a non-terminal record moves to **Likely Stuck at Google (60+ days)**.
- Explicit Google failures are shown immediately in **Errors / Attention**.
- Temporary status-check failures remain retryable and are not immediately treated as upload failures.
- Completed and definitive failed records are not refreshed unnecessarily.

## Optional Nadir processing

The optional Nadir feature hides the camera mount, tripod or vehicle-roof area using a bundled or custom PNG.

Features include:

- Restricted PNG-only ImageMagick processing.
- Automatic patch scaling.
- Equirectangular 360-degree support.
- Patch caching.
- Adaptive parallel encoding.
- Hardware-encoder testing.
- 8-bit and 10-bit video handling.
- Preservation of equirectangular projection metadata.
- Codec-aware capacity, including one heavy CineForm task at a time.

## GPU encoding

Supported acceleration routes depend on the installed hardware and bundled FFmpeg build:

- NVIDIA NVENC.
- Intel Quick Sync Video.
- AMD AMF.
- Software `libx265` fallback where appropriate.

Automatic mode uses FFmpeg 9.1. FFmpeg 8.1.1 remains available as an automatic NVENC compatibility fallback for older NVIDIA drivers.

## GoPro HERO and Mission 1 workflow

- Dedicated processing for standard MP4/MOV footage.
- GoPro Mission 1 support through the HERO workflow.
- Internal GPMF handling.
- Configurable frame-sampling distance.
- FFmpeg frame extraction.
- GPS validation and review.
- Mapillary processing and optional upload.
- Shared monitoring, result-store, cleanup and reporting architecture with the MAX workflow where technically applicable.

Run resume is intentionally available only for the MAX workflow. Normal Pause/Continue during an active run remains separate.

## Workflow monitoring and final reporting

- Stable per-item identities across all phases.
- Central thread-safe run result store.
- Separate GPS, Mapillary, Street View, upload and cleanup results.
- Route distance stored once per item and reused without a final GPX rescan.
- Dynamic waiting queues that exclude active tasks.
- Responsive GUI updates with coalesced progress output.
- `Needs_Review` output for rejected, skipped and failed items.
- Verified cleanup with source and destination checks.
- Frozen results before final reporting.
- No expensive final ffprobe, GPX or JPEG rescan during normal reporting.
- Synchronized TXT and XML log completion.

## Requirements

The recommended option is the compiled Windows `.exe` release. Required command-line utilities and portable dependencies are included in the packaged release.

### Running from Python source

A source installation requires:

1. Python 3.x.
2. FFmpeg and FFprobe.
3. ExifTool.
4. Mapillary Tools.
5. ImageMagick or the packaged portable ImageMagick directory.
6. Required Python dependencies such as Pillow, tkintermapview and pywebview where used.
7. A valid `resources/google_oauth_desktop.json` when building a distribution with Google Street View upload.

The application expects bundled runtimes under `tools/`. Runtime locations are not intended as normal end-user configuration fields.

## Basic configuration

1. Select the source and target directories.
2. Select **Automatic (FFmpeg 9.1)** unless a specific compatibility version is required.
3. Select or authenticate the local Mapillary profile if Mapillary upload is required.
4. Configure Mapillary sample distance and upload workers.
5. Under **Google Street View upload**, sign in with Google if Street View upload is required.
6. Select the MAX or HERO/Mission 1 workflow.
7. Choose the required processing and upload actions.
8. Configure quality, GPU and optional Nadir settings.
9. Start the workflow.
10. Review GPS decisions, monitor status and final summaries.

## Important notes

> [!WARNING]
> Standard VLC cannot replace GoPro Player for converting proprietary GoPro MAX `.360` footage into a correctly stitched equirectangular video.

- Keep each `.360` file and stitched video under the same base name.
- GPS recovery is intentionally fail-safe.
- No synthetic GPS positions or timestamps are generated.
- A successful GPS correction does not replace final MP4/GPX synchronization checks.
- Google Street View and Mapillary uploads are separate actions with separate statuses.
- Always review the GPS preflight, recovery, correction and final result summaries.

## Logging and troubleshooting

The workflow creates standard and Extended Output Logs. Extended logs are available as TXT and XML.

When reporting an issue, include:

- Application version and build ID.
- Camera family and recording mode.
- Source codec.
- Enabled workflow phases.
- Relevant final summary tables.
- GPX rejection code, when applicable.
- Approximately 30 to 50 lines around the first warning or error.

Useful prefixes include:

```text
[GPS PREFLIGHT]
[GPS PREFLIGHT OK]
[GPS PREFLIGHT REJECTED]
[GPS ITERATIVE FIX]
[GPS ROUTING]
[GPS FIX]
[GPS REVIEW]
[GPS SUMMARY]
[MAPILLARY SAMPLE COVERAGE]
[MAPILLARY GPS AUTHORITY]
[SVS API]
[FINAL CLEANUP COMPLETE]
[RUN RESULTS FINALIZED]
[FINAL REPORT GENERATION START]
[FINAL REPORT GENERATION COMPLETE]
```

## Development history

### Version 6.7 development line

- Adopted FFmpeg 9.1 as the automatic default.
- Adopted ExifTool 13.64 and Mapillary Tools 0.15.1.
- Added a bundled production Google Desktop OAuth client.
- Added optional Google Street View upload and status management.
- Added serial Street View upload dispatching.
- Added sample-range protection before Mapillary GPS override.
- Expanded distributed GPS authority verification.
- Added central result-store based route distance and final reporting.
- Improved startup splash behavior for packaged one-file builds.
- Changed the Google likely-stuck threshold to 60 days.

### 28 July 2026: Version 5.7.0

- Added iterative GPS-track recovery.
- Added complete route rebuilding after each accepted correction.
- Added multi-point cluster recovery.
- Added course, acceleration, bridge-speed and route-corridor checks.
- Added dynamic cycling limits and the `urban_fast` profile.
- Added structured GPS preflight and recovery summaries.

### 1 June 2026: Mission 1 support

- Added GoPro Mission 1 support through the standard HERO workflow.

### 20 April 2026: Version 5.2.0

- Added supported TimeWarp processing for GoPro MAX 1 and MAX 2.

### 15 December 2025: Version 4.2.2

- Added GPU-accelerated encoding for Nadir-processed video.

## License and third-party components

This project uses external utilities and libraries that remain subject to their own licenses.

Review the included license and notice files for:

- FFmpeg and FFprobe.
- ExifTool.
- Mapillary Tools.
- ImageMagick.
- Python dependencies.

## Disclaimer

GoPro Workflow is an independent project and is not endorsed by, sponsored by or affiliated with GoPro, Meta, Mapillary or Google. Product and service names belong to their respective owners.
