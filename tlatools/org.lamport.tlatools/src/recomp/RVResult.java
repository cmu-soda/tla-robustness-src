package recomp;

import cmu.isr.ts.LTS;

public class RVResult {
    private String msg;
    private LTS lts;
    private boolean isSetYet = false;

    public RVResult() {
        msg = null;
        lts = null;
        isSetYet = false;
    }

    public synchronized void setIfWinner(String msg, LTS lts) {
        if (!isSetYet){
            this.msg = msg;
            this.lts = lts;
            this.isSetYet = true;
        }
    }

    public String getMsg() {
        return msg;
    }

    public LTS getLTS() {
        return lts;
    }

    public boolean isSetYet() {
        return isSetYet;
    }

}
