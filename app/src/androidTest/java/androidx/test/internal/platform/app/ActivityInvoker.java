package androidx.test.internal.platform.app;

import android.app.Activity;
import android.app.Instrumentation;
import android.content.Intent;
import android.os.Bundle;

public interface ActivityInvoker {
    Instrumentation.ActivityResult getActivityResult();
    Intent getIntentForActivity(Class<? extends Activity> activityClass);
    void finishActivity(Activity activity);
    void pauseActivity(Activity activity);
    void recreateActivity(Activity activity);
    void resumeActivity(Activity activity);
    void startActivity(Intent intent);
    void startActivity(Intent intent, Bundle options);
    void startActivityForResult(Intent intent);
    void startActivityForResult(Intent intent, Bundle options);
    void stopActivity(Activity activity);
}
