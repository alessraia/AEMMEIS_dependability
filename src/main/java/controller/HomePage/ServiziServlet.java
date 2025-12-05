package controller.HomePage;

import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletException;
import jakarta.servlet.annotation.WebServlet;
import jakarta.servlet.http.HttpServlet;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import jakarta.servlet.http.HttpSession;
import model.utenteService.Utente;

import java.io.IOException;

@WebServlet("/services")
public class ServiziServlet extends HttpServlet {
    protected void doGet(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
        // Imposta il tipo di contenuto
        //response.setContentType("text/html;charset=UTF-8");

        // Inoltra la richiesta alla JSP
        RequestDispatcher dispatcher = request.getRequestDispatcher("/WEB-INF/results/services.jsp");
        try {
            dispatcher.forward(request, response);
        } catch (ServletException e) {
            log("Errore durante il forward verso /WEB-INF/results/about-us.jsp", e);

        } catch (IOException e) {
            log("Errore di I/O durante il forward verso /WEB-INF/results/about-us.jsp", e);

        }
    }
}
