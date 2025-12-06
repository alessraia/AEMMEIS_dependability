package controller.utils;

import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletResponse;

import java.io.IOException;

public final class ControlMethod {

    private ControlMethod() {
        // Impedisce l'istanza: è una utility class
    }

    public static void safeRedirect(HttpServletResponse response, String location,
                                    HttpServlet servlet) {
        try {
            response.sendRedirect(location);
        } catch (IOException e) {
            servlet.log("Errore durante il redirect verso " + location, e);
        }
    }
    public static void safeSendError(HttpServletResponse response,
                                 int statusCode,
                                 String message, HttpServlet servlet) {
        try {
            response.sendError(statusCode, message);
        } catch (IOException e) {
            servlet.log("Errore durante sendError " + statusCode + " - " + message, e);
        }
    }
}
