Don't use the 4.1.0 version, there is a Mapillary upload bug present for the GoPro Max workflow. Please use 4.1.3 or higher.
# GoPro Max & Hero - Mapillary & SVS Workflow Tool

A comprehensive GUI application written in Python to process video footage from the **GoPro Max (360°)** and **GoPro Hero (Standard)** for upload to **Mapillary** and **StreetView Studio (SVS)**.

This tool automates the process of sampling, GPMF metadata extraction, GPS corrections, and uploading.

## ✨ Features

* **GUI Interface:** User-friendly interface (Tkinter) with tabs for configuration, logs, and progress tracking.
* **GoPro Max Workflow (360°):**
    * Support for Max 1 & Max 2 logic.
    * GPMF metadata extraction and muxing.
    * **StreetView Studio Fix:** Automatic correction of MP4 headers and GPX timestamps for SVS compatibility.
    * **Nadir Patch (Optional):** Hides the tripod using a custom logo (requires ImageMagick).
* **GoPro Hero Workflow:**
    * Dedicated workflow for standard MP4 files.
    * Automatic sampling and processing for Mapillary.
* **Mapillary Integration:** Direct upload using Mapillary Tools (integrated command).

## 🚀 Requirements

To use this tool, the following external utilities must be installed on your system (or placed in the `tools/` folder):

1.  **Python 3.x**
2.  **FFmpeg & FFprobe:** For video processing and frame extraction.
3.  **ExifTool:** For metadata manipulation and GPX generation.
4.  **Mapillary Tools:** The official CLI tool for uploads.
5.  **ImageMagick:** (Optional) Only required if using the Nadir Patch feature.

### Python Dependencies
Install the required Python libraries using:

```bash
pip install Pillow

🛠️ Installation & Usage
Clone this repository or download the script.

Ensure your source files (.360 files must be converted to .mp4 using GoPro Player first!) are in a source folder.

Run the script:
python GoPro_Mapillary_SVS_Workflow_v4.1.0.py

Configuration Tab:

Select your Source and Target directories.

Point the paths to exiftool.exe, ffmpeg.exe, etc.

Enter your Mapillary username.

Choose the desired workflow (Max or Hero) and click START.

Or download the .exe file with all the tools included.
