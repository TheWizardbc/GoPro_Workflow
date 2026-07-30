# GoPro MAX & HERO/Mission 1 Series Mapillary and Street View Studio Workflow Tool

A comprehensive Windows GUI application written in Python for processing footage from the **GoPro MAX 1**, **GoPro MAX 2**, **GoPro HERO series**, and **GoPro Mission 1 series** for use with **Mapillary** and **Google Street View Studio (SVS)**.

The application automates video preparation, GPMF metadata extraction and muxing, GPX generation, GPS validation and recovery, Nadir patching, frame sampling, Mapillary processing, uploading, and SVS timestamp synchronization.

> [!IMPORTANT] 
> Version 5.8.9 and above have an automated version checker, it's recommended to update to >5.8.9.

## Support the project

If this tool saves you time and you would like to buy me a coffee:

[https://www.paypal.com/paypalme/mfaken](https://www.paypal.com/paypalme/mfaken)

## Features

### Graphical user interface

- User-friendly Tkinter-based Windows interface.
- Separate workflows for GoPro MAX and standard GoPro cameras.
- Configuration options for source and target directories, external utilities, video quality, GPU encoding, Nadir processing, and Mapillary credentials.
- Standard and extended workflow logs.
- Detailed progress reporting.
- Per-file workflow phase tracking.
- Clear final accept/reject summaries.
- Per-file GPS correction and recovery tables.
- Persistent JSON-based settings.

### GoPro MAX 360-degree workflow

#### Camera support

- GoPro MAX 1 (2019 and 2025 version)
- GoPro MAX 2

#### Video-mode support

- Standard video
- Supported TimeWarp modes 2x and 5x
- MAX 1 and MAX 2 workflow routing
- Automatic distinction between standard and TimeWarp footage

#### Supported stitched video formats

- GoPro CineForm
- HEVC/H.265
- H.264

#### Automated preparation

- Automatic matching of stitched video and original `.360` files.
- Automatic GPMF stream detection and extraction.
- MAX 2 legacy GPMF stream compatibility.
- GPMF metadata muxing into prepared video files.
- Metadata transfer from the original `.360` file.
- Video-stream validation using FFprobe.
- Automatic handling of 8-bit and 10-bit video.
- Preservation of equirectangular projection metadata where supported.

## Early GPS preflight

GPS is checked directly after the GPMF stream has been extracted and before expensive video processing starts.

The early GPS preflight can detect:

- Missing GPS data
- Missing timestamps
- Empty timestamps
- Invalid timestamps
- Duplicate timestamps
- Locally backward timestamps
- Non-monotonic timestamps
- Invalid coordinates
- Unrealistic speed discontinuities
- Isolated GPS jumps
- Displaced GPS clusters
- GPS continuity gaps
- Insufficient timed GPS anchors

When a file cannot be recovered safely and is not required by another enabled workflow, the application skips unnecessary:

- Nadir encoding
- Video and GPMF muxing
- Metadata transfer
- SVS GPX generation
- SVS header correction

This prevents lengthy video processing for footage that cannot be used safely by Street View Studio.

## GPS normalization and recovery

The GPS correction system uses the original timestamps and coordinates contained in the GoPro GPMF telemetry.

> [!IMPORTANT]
> The application does not invent or interpolate GPS timestamps or positions.

Supported GPS normalization and correction operations include:

- Removal of coordinate samples without timestamps
- Removal of isolated invalid points
- Recovery of duplicate timestamps
- Removal of limited locally backward timestamps
- Correction of isolated GPS speed jumps
- Correction of short displaced GPS sequences
- Iterative recovery of multi-point GPS clusters
- Removal of a safely identifiable faulty final GPS tail
- Complete post-correction validation

After every accepted iterative correction, the active GPS track is rebuilt and all speed segments are recalculated.

This prevents subsequent decisions from being based on outdated point indexes or GPS segments that no longer exist.

## Iterative GPS recovery

Difficult GPS tracks are processed iteratively:

1. Detect the worst remaining GPS discontinuity.
2. Test multiple possible point-removal windows.
3. Evaluate each possible replacement bridge.
4. Apply the safest valid candidate.
5. Rebuild the complete active GPS track.
6. Recalculate all distances, speeds, courses, and acceleration transitions.
7. Search for the next remaining discontinuity.
8. Continue until the track is stable or cannot be recovered safely.
9. Run complete post-recovery validation.

### Recovery limits

- Maximum of 12 points per local recovery candidate
- Maximum of 30 removed timed points per complete track
- Maximum of 10 recovery rounds
- Maximum bridge duration of 10 seconds
- No coordinate interpolation
- No timestamp interpolation
- No point reordering
- Complete final-track validation

If a complete and safe repair cannot be found, the GPX file is rejected and quarantined.

## Movement-profile detection

GPS tracks are classified using a robust speed distribution rather than one maximum-speed value.

The analysis includes:

- Average speed
- Median speed
- P75
- P90
- P95
- Proportion of faster segments
- Filtered classification samples
- Local median speed

Supported movement profiles include:

- `walking`
- `cycling`
- `urban_fast`
- `driving`

### Urban fast

The `urban_fast` profile represents the overlap between:

- A fast bicycle
- A racing bicycle
- A speed-pedelec
- A motor vehicle moving through urban traffic

Speed percentiles alone cannot always reliably distinguish a fast bicycle from an urban car. The overlap profile therefore uses a conservative dynamic correction limit and additional route analysis.

## Dynamic GPS correction limits

The GPS speed limit used for correction depends on the detected movement profile.

### Walking

Walking uses a conservative correction limit:

```text
30 km/h
```

### Cycling

Cycling uses a dynamic correction limit:

```text
max(
    65 km/h,
    P95 x 1.6,
    P90 x 1.8,
    median x 2.5
)
```

The result is bounded between:

```text
65 and 90 km/h
```

This allows legitimate high speeds from racing bicycles, fast e-bikes, speed-pedelecs, and downhill cycling. A legitimate speed above 50 km/h is therefore not automatically treated as a GPS error.

### Urban fast

Ambiguous fast-bicycle or urban-driving tracks use:

```text
max(
    80 km/h,
    P95 x 1.6,
    P90 x 1.8,
    median x 2.5
)
```

The result is bounded between:

```text
80 and 120 km/h
```

### Driving

Driving uses:

```text
max(
    150 km/h,
    P95 x 2
)
```

The result is bounded between:

```text
150 and 250 km/h
```

> [!NOTE]
> A GPS point is never removed only because the calculated speed exceeds the active profile limit. The application also examines the surrounding route and the result of removing the suspected point or cluster.

## Advanced GPS recovery checks

For difficult GPS discontinuities, the application evaluates multiple possible recovery windows.

The analysis includes:

- Bridge distance
- Bridge duration
- Bridge speed
- Local median speed
- Incoming speed
- Outgoing speed
- Incoming course
- Outgoing course
- Course change across the bridge
- Acceleration around the recovered transition
- Distance from suspicious points to the expected route corridor
- Number of points requiring removal
- Remaining GPS discontinuities after rebuilding the track

### Course validation

Course changes are evaluated as a hard safety condition. A recovery candidate with an excessive course change is rejected, even when the bridge speed is below the active speed limit.

### Acceleration validation

| Movement profile | Maximum transition deviation |
| --- | ---: |
| Walking | 20 km/h/s |
| Cycling | 35 km/h/s |
| Urban fast | 50 km/h/s |
| Driving | 80 km/h/s |

These values are used together with speed, course, route-corridor, and bridge checks.

## GPS preflight reporting

Immediately after the early GPS preflight, the application displays structured summary tables.

### GPS PREFLIGHT SUMMARY

The summary shows per file:

- File name
- Result
- Movement profile
- Original point count
- Final point count
- Total removed points
- Points without timestamps
- Duplicate timestamps
- Backward timestamps
- Isolated GPS jumps
- Multi-point removals
- Active correction limit
- Approval or rejection reason

Example:

```text
File         | Result   | Profile | Original | Final | Removed | No time | Dup | Back | Jump | Multi | Limit | Reason
-------------+----------+---------+----------+-------+---------+---------+-----+------+------+-------+-------+----------------
GS010123.mov | OK       | driving | 4481     | 4480  | 1       | 1       | 0   | 0    | 0    | 0     | 171.0 | GPS validated
GS010124.mov | REJECTED | driving | 4481     | 0     | 0       | 1       | 0   | 0    | 0    | 0     | 154.9 | Unsafe course
```

### GPS RECOVERY ATTEMPTS

When iterative recovery is attempted, a second table shows:

- File name
- Recovery round
- Applied or rejected result
- Number of points involved
- Bridge speed
- Course change
- Acceleration
- Explanation

Example:

```text
File         | Round | Result   | Removed | Bridge | Course | Accel | Explanation
-------------+-------+----------+---------+--------+--------+-------+-------------------------------
GS010124.mov | 1     | APPLIED  | 4       | 92.4   | 64.2   | 21.5  | Applied; track rebuilt
GS010124.mov | 2     | REJECTED | 8       | 138.1  | 229.1  | 63.7  | Unsafe course change
```

## Final GPS Correction Summary

The final GPS Correction Summary uses the same table layout as the other workflow summaries.

Removed GPS points are separated by correction type:

- `No time`
- `Dup time`
- `Back time`
- `GPS jump`
- `Multi`
- `Invalid`

This makes it clear why GPS points were removed.

## Street View Studio preparation

- Automatic GPX generation from GoPro GPMF telemetry
- Automatic GPS normalization and recovery
- Automatic creation of SVS-compatible MP4 and GPX pairs
- Automatic synchronization of the MP4 QuickTime header with the first valid GPX timestamp
- Verification of all critical QuickTime date fields
- Separate handling for MAX 1 Standard, MAX 2 Standard, and supported TimeWarp footage
- Removal of superseded files after successful verification
- Fail-safe rejection when an SVS pair cannot be prepared reliably

### Synchronized QuickTime fields

- Create Date
- Modify Date
- Track Create Date
- Track Modify Date
- Media Create Date
- Media Modify Date

## Heavy-processing exclusion

When GPS is rejected during the early preflight and Mapillary does not require the file, the application excludes that file from:

- Nadir encoding
- Video and GPMF muxing
- Metadata transfer
- MAX 1 export
- MAX 2 GPX generation
- SVS header correction

The log reports:

```text
[GPS ROUTING] filename: Nadir, mux and metadata stages skipped after failed GPS preflight.
```

This can save substantial processing time for high-resolution 360-degree footage.

## Optional Nadir patch

The optional Nadir Patch feature hides the camera mount, tripod, or vehicle-roof area using a custom image.

Features include:

- ImageMagick-based patch preparation
- Automatic patch scaling
- Equirectangular 360-degree support
- Patch caching
- Parallel video encoding
- Automatic hardware-encoder testing
- 8-bit and 10-bit processing
- Preservation of the equirectangular projection
- Configurable Nadir image and scale factor

> [!NOTE]
> ImageMagick must be installed separately to use the Nadir Patch feature.

## GPU encoding

Supported hardware-accelerated routes depend on the installed hardware and FFmpeg build:

- NVIDIA NVENC
- Intel Quick Sync Video
- AMD AMF

The application can test the selected encoder before processing the complete batch. Software encoding can be used when a compatible hardware encoder is unavailable.

GPU encoding can significantly reduce processing time for high-resolution Nadir-patched 360-degree video.

## GoPro HERO and Mission 1 workflow

- Dedicated processing for standard MP4 footage
- Out-of-the-box GoPro Mission 1 series support
- Configurable frame-sampling intervals
- Frame extraction using FFmpeg
- Metadata and camera-information handling
- GPS safety checks
- Mapillary image processing
- Optional direct upload using Mapillary Tools

## Mapillary integration

- Integrated Mapillary Tools support
- Frame sampling from supported videos
- Processing of sampled images
- Optional direct upload
- Configurable Mapillary username
- Separate controls for sampling, processing, and uploading
- Upload-only workflow support
- Clear upload status reporting
- Safe cleanup of processed files

## Requirements

The recommended option for most users is the compiled Windows `.exe` release.

The required command-line utilities are included in the packaged release unless otherwise stated. ImageMagick must be installed separately when using the optional Nadir Patch feature.

### Running the Python source

Running the Python script directly requires:

1. Python 3.x
2. FFmpeg
3. FFprobe
4. ExifTool
5. Mapillary Tools
6. ImageMagick, optional for Nadir Patch processing

The application can use tools placed in the bundled `tools/` directory or paths selected manually in the configuration interface.

## Basic configuration

1. Select the source directory.
2. Select the target directory.
3. Configure paths to FFmpeg, FFprobe, ExifTool, the GPX format file, Mapillary Tools, and optionally ImageMagick.
4. Enter the Mapillary username when using Mapillary.
5. Select the GoPro MAX Workflow or GoPro HERO/Mission 1 Workflow.
6. Enable the required processing phases.
7. Configure video quality and GPU settings.
8. Configure sampling and Nadir options.
9. Click **START**.
10. Review the GPS preflight and final summary tables.

Alternatively, download the compiled `.exe` release with the required tools included.

## Typical GoPro MAX source layout

Matching MAX files must use the same base filename.

Example using CineForm:

```text
GS010123.360
GS010123.mov
```

Example using H.264 or HEVC:

```text
GS010123.360
GS010123.mp4
```

The `.360` file supplies the original GoPro GPMF telemetry. The matching `.mov` or `.mp4` file supplies the stitched equirectangular video exported by GoPro Player.

## Important notes

> [!WARNING]
> Standard VLC cannot replace GoPro Player for converting proprietary GoPro MAX `.360` footage into a correctly stitched equirectangular video.

Export MAX footage using GoPro Player or another compatible GoPro MAX stitching solution before using the footage with this workflow.

Additional notes:

- Keep the `.360` file and stitched video under the same base filename.
- GPS recovery is intentionally fail-safe.
- The application does not generate synthetic GPS positions.
- The application does not generate synthetic GPS timestamps.
- An unrecoverable GPX file is quarantined.
- A successful GPX correction does not replace the final MP4/GPX synchronization checks.
- Always review the GPS Preflight Summary, GPS Recovery Attempts, GPS Correction Summary, and Final Accept/Reject Summary.

## Development history

### 28 July 2026: Version 5.7.0

- Added iterative GPS-track recovery.
- Added complete track rebuilding after each accepted correction.
- Added multi-point GPS cluster recovery.
- Added course validation.
- Added acceleration validation.
- Added bridge-speed and route-corridor checks.
- Added dynamic cycling limits for fast bicycles and speed-pedelecs.
- Added the `urban_fast` overlap profile.
- Added GPS Preflight Summary tables.
- Added GPS Recovery Attempts tables.
- Expanded the final GPS Correction Summary.
- Added separate GPS removal-type columns.
- Added heavy-processing exclusion after failed GPS preflight.
- Improved fail-safe GPX rejection.
- Improved recovery diagnostics and workflow routing.

### 1 June 2026: Mission 1 support

- Added GoPro Mission 1 series support.
- Mission 1 uses the standard HERO workflow.
- Out-of-the-box processing support is included.

### 20 April 2026: Version 5.2.0

- Added supported TimeWarp processing for GoPro MAX 1 and MAX 2.
- TimeWarp support was initially intended primarily for Street View Studio output.

### 15 December 2025: Version 4.2.2

- Added GPU-accelerated encoding.
- Significantly reduced processing time for Nadir-patched videos.

## Logging and troubleshooting

The workflow creates standard and extended log files.

When reporting an issue, include:

- Application version
- Camera family
- Source-video codec
- Enabled workflow phases
- Relevant final summary tables
- GPX rejection code, if applicable
- Approximately 30 to 50 log lines around the first warning or error

Useful GPS-related log prefixes include:

```text
[GPS PREFLIGHT]
[GPS PREFLIGHT OK]
[GPS PREFLIGHT REJECTED]
[GPS ITERATIVE FIX]
[GPS ROUTING]
[GPS FIX]
[GPS REVIEW]
[GPS SUMMARY]
```

## License and third-party components

This project uses external utilities and libraries that remain subject to their own licenses.

Review the included license and notice files for:

- FFmpeg and FFprobe
- ExifTool
- Mapillary Tools
- ImageMagick
- Python dependencies
