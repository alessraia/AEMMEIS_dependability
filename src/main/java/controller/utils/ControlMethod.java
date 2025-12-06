package controller.utils;

import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletResponse;

import java.io.IOException;

public class ControlMethod {
    public static void safeRedirect(HttpServletResponse response, String location,
                                    HttpServlet servlet) {
        try {
            response.sendRedirect(location);
        } catch (IOException e) {
            servlet.log("Errore durante il redirect verso " + location, e);
        }
    }
}
