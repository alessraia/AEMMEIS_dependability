package controller.HomePage;

import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletException;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;

import java.io.IOException;

@WebServlet("/about-us")
public class AboutUsServlet extends HttpServlet {

    @Override
    protected void doGet(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {

        // Inoltra la richiesta alla JSP
        RequestDispatcher dispatcher =
                request.getRequestDispatcher("/WEB-INF/results/about-us.jsp");
        try {
            dispatcher.forward(request, response);
        } catch (ServletException e) {
            log("Errore durante il forward verso /WEB-INF/results/about-us.jsp", e);
            throw e;
        } catch (IOException e) {
            log("Errore di I/O durante il forward verso /WEB-INF/results/about-us.jsp", e);
            throw e;
        }
    }
}
