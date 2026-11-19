# ScreenBreak manual report email

This build sends email only after the user clicks **Send report now**. It does not send reports automatically, install a scheduled email trigger, or upload report snapshots in the background.

## Use it on the configured Windows profile

1. Open ScreenBreak and choose **Settings > Report email**.
2. Enter the recipient email address.
3. Click **Send report now**.

The current Windows profile already has its Google service connection saved in `%LOCALAPPDATA%\ScreenBreak`. The access key stays in local app data and is not shown in the settings screen or included in this ZIP. Google sends from the account that authorized the Apps Script service.

## If you use a different Windows profile or Google account

Create your own Apps Script project from `Google-Apps-Script.gs`, run `setupScreenBreak`, and deploy it as a web app that executes as you. Keep its URL and access key private. The current app UI is intentionally set up for the existing Windows profile; do not copy or publish another account's access key in a shared package.

## What the manual send does

When the user clicks **Send report now**, ScreenBreak builds the report and sends it to the entered recipient through Google. The app must be open and online while the request is sent. Google does not retain the submitted report snapshot for future scheduled emails.

Settings are backed up at `%LOCALAPPDATA%\ScreenBreak\screenbreak_settings.json`, outside the extracted program folder. The app restores these settings when this build is opened after replacing its program files.
