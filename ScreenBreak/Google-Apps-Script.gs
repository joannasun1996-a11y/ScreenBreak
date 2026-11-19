/** ScreenBreak manual report email service.
 * The script owner authorizes MailApp. Scheduled email triggers are removed.
 * Requests require the private setup-generated access key.
 */
const PROP = PropertiesService.getScriptProperties();
const TOKEN_KEY = 'SCREENBREAK_ACCESS_KEY';
const TRIGGER_HANDLER = 'checkAndSendScreenBreakReport';

function setupScreenBreak() {
  let token = PROP.getProperty(TOKEN_KEY);
  if (!token) {
    token = Utilities.getUuid().replace(/-/g, '') + Utilities.getUuid().replace(/-/g, '');
    PROP.setProperty(TOKEN_KEY, token);
  }
  deleteScheduledTriggers_();
  MailApp.getRemainingDailyQuota();
  Logger.log('Manual ScreenBreak report sending is ready. No schedule or trigger is installed.');
}

/** One-time migration: cancel the old scheduled email and clear its schedule. */
function disableScheduledScreenBreakEmails() {
  deleteScheduledTriggers_();
  PROP.deleteProperty('SCREENBREAK_SETTINGS');
  PROP.deleteProperty('SCREENBREAK_LAST_SENT_DATE');
  Logger.log('Scheduled emails are disabled. Manual Send report now remains available.');
}

function doPost(e) {
  try {
    const body = JSON.parse(e && e.postData && e.postData.contents || '{}');
    const savedToken = PROP.getProperty(TOKEN_KEY);
    if (!savedToken || !constantTimeEquals_(String(body.token || ''), savedToken)) {
      return json_({ok: false, error: 'Invalid access key.'});
    }
    if (String(body.action || '') !== 'send_now') {
      return json_({ok: false, error: 'Only Send report now is enabled.'});
    }
    const settings = body.settings || {};
    const report = body.report || {};
    validateRecipient_(settings.recipient);
    validateReport_(report);
    sendReport_(settings, report);
    return json_({ok: true, sent_now: true});
  } catch (err) {
    console.error(err && err.stack || err);
    return json_({ok: false, error: String(err && err.message || err).slice(0, 500)});
  }
}

/** Keep compatibility if manually run; this function never sends email. */
function checkAndSendScreenBreakReport() {
  deleteScheduledTriggers_();
  Logger.log('Scheduled sending is disabled.');
}

function stopScreenBreakCloudEmail() {
  disableScheduledScreenBreakEmails();
  PROP.deleteProperty(TOKEN_KEY);
  Logger.log('ScreenBreak manual email service stopped and access key deleted.');
}

function deleteScheduledTriggers_() {
  ScriptApp.getProjectTriggers().forEach(function (trigger) {
    if (trigger.getHandlerFunction() === TRIGGER_HANDLER) ScriptApp.deleteTrigger(trigger);
  });
}

function sendReport_(settings, report) {
  const attachments = (report.attachments || []).map(function (item) {
    return Utilities.newBlob(String(item.html || ''), 'text/html', String(item.filename || 'report.html'));
  });
  MailApp.sendEmail({
    to: settings.recipient,
    subject: String(report.subject || 'ScreenBreak report').slice(0, 250),
    body: String(report.plain || 'Your ScreenBreak report is attached.'),
    htmlBody: String(report.html || ''),
    attachments: attachments,
    name: 'ScreenBreak'
  });
}

function validateRecipient_(recipient) {
  if (!/^[^\s@]+@[^\s@]+\.[^\s@]+$/.test(String(recipient || ''))) {
    throw new Error('Enter a valid report recipient email.');
  }
}

function validateReport_(report) {
  if (!report || !/^\d{4}-\d{2}-\d{2}$/.test(String(report.date || '')) || !report.html || !report.plain) {
    throw new Error('Report is missing. Save or open the report, then try again.');
  }
  if (Utilities.newBlob(JSON.stringify(report)).getBytes().length > 5 * 1024 * 1024) {
    throw new Error('Report exceeds the email service size limit (5 MB).');
  }
}

function constantTimeEquals_(a, b) {
  let mismatch = a.length ^ b.length;
  const length = Math.max(a.length, b.length);
  for (let i = 0; i < length; i++) mismatch |= (a.charCodeAt(i) || 0) ^ (b.charCodeAt(i) || 0);
  return mismatch === 0;
}

function json_(value) {
  return ContentService.createTextOutput(JSON.stringify(value)).setMimeType(ContentService.MimeType.JSON);
}
