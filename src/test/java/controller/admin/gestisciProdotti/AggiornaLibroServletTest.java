package controller.admin.gestisciProdotti;

import model.libroService.Libro;
import model.libroService.LibroDAO;
import org.junit.jupiter.api.Test;
import org.mockito.MockedConstruction;

import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;

import static org.mockito.Mockito.*;

public class AggiornaLibroServletTest {

    @Test
    public void missingParameter_forwardsToError() throws Exception {
        HttpServletRequest request = mock(HttpServletRequest.class);
        HttpServletResponse response = mock(HttpServletResponse.class);
        RequestDispatcher dispatcher = mock(RequestDispatcher.class);

        when(request.getParameter("titolo")).thenReturn(null); // missing
        when(request.getParameter("isbn")).thenReturn("ISBN1");
        when(request.getParameter("annoPubb")).thenReturn("2020");
        when(request.getParameter("genere")).thenReturn("Fiction");
        when(request.getParameter("prezzo")).thenReturn("9.99");
        when(request.getParameter("sconto")).thenReturn("10");
        when(request.getParameter("trama")).thenReturn("trama");
        when(request.getParameter("immagine")).thenReturn("img.jpg");

        when(request.getRequestDispatcher("/WEB-INF/errorJsp/erroreForm.jsp")).thenReturn(dispatcher);

        new AggiornaLibroServlet().doGet(request, response);

        verify(dispatcher, times(1)).forward(request, response);
    }

    @Test
    public void invalidPrezzo_forwardsToError_noUpdate() throws Exception {
        HttpServletRequest request = mock(HttpServletRequest.class);
        HttpServletResponse response = mock(HttpServletResponse.class);
        RequestDispatcher dispatcher = mock(RequestDispatcher.class);

        when(request.getParameter("titolo")).thenReturn("Titolo");
        when(request.getParameter("isbn")).thenReturn("ISBN2");
        when(request.getParameter("annoPubb")).thenReturn("2021");
        when(request.getParameter("genere")).thenReturn("NonFiction");
        when(request.getParameter("prezzo")).thenReturn("not-a-number");
        when(request.getParameter("sconto")).thenReturn("5");
        when(request.getParameter("trama")).thenReturn("trama");
        when(request.getParameter("immagine")).thenReturn("img2.jpg");

        when(request.getRequestDispatcher("/WEB-INF/errorJsp/erroreForm.jsp")).thenReturn(dispatcher);

        try (MockedConstruction<LibroDAO> mocked = mockConstruction(LibroDAO.class)) {
            new AggiornaLibroServlet().doGet(request, response);

            verify(dispatcher, times(1)).forward(request, response);
            // ensure no updateLibro call
            for (LibroDAO dao : mocked.constructed()) {
                verify(dao, never()).updateLibro(any());
            }
        }
    }

    @Test
    public void invalidSconto_forwardsToError_noUpdate() throws Exception {
        HttpServletRequest request = mock(HttpServletRequest.class);
        HttpServletResponse response = mock(HttpServletResponse.class);
        RequestDispatcher dispatcher = mock(RequestDispatcher.class);

        when(request.getParameter("titolo")).thenReturn("Titolo");
        when(request.getParameter("isbn")).thenReturn("ISBN3");
        when(request.getParameter("annoPubb")).thenReturn("2022");
        when(request.getParameter("genere")).thenReturn("SciFi");
        when(request.getParameter("prezzo")).thenReturn("12.5");
        when(request.getParameter("sconto")).thenReturn("abc"); // invalid
        when(request.getParameter("trama")).thenReturn("trama");
        when(request.getParameter("immagine")).thenReturn("img3.jpg");

        when(request.getRequestDispatcher("/WEB-INF/errorJsp/erroreForm.jsp")).thenReturn(dispatcher);

        try (MockedConstruction<LibroDAO> mocked = mockConstruction(LibroDAO.class)) {
            new AggiornaLibroServlet().doGet(request, response);

            verify(dispatcher, times(1)).forward(request, response);
            for (LibroDAO dao : mocked.constructed()) {
                verify(dao, never()).updateLibro(any());
            }
        }
    }

    @Test
    public void validInput_callsUpdateAndForwardsToModificaLibro() throws Exception {
        HttpServletRequest request = mock(HttpServletRequest.class);
        HttpServletResponse response = mock(HttpServletResponse.class);
        RequestDispatcher dispatcher = mock(RequestDispatcher.class);

        when(request.getParameter("titolo")).thenReturn("Good Book");
        when(request.getParameter("isbn")).thenReturn("ISBN4");
        when(request.getParameter("annoPubb")).thenReturn("2023");
        when(request.getParameter("genere")).thenReturn("Drama");
        when(request.getParameter("prezzo")).thenReturn("15.0");
        when(request.getParameter("sconto")).thenReturn("20");
        when(request.getParameter("trama")).thenReturn("Good trama");
        when(request.getParameter("immagine")).thenReturn("img4.jpg");

        when(request.getRequestDispatcher("modifica-libro")).thenReturn(dispatcher);

        try (MockedConstruction<LibroDAO> mocked = mockConstruction(LibroDAO.class,
                (mock, context) -> {
                    // do nothing on update
                })) {

            new AggiornaLibroServlet().doGet(request, response);

            // verify updateLibro was called with a Libro that has isbn set
            boolean called = false;
            for (LibroDAO dao : mocked.constructed()) {
                try {
                    verify(dao, times(1)).updateLibro(argThat(l -> l.getIsbn().equals("ISBN4") && l.getTitolo().equals("Good Book")));
                    called = true;
                } catch (Throwable t) {
                    // ignore
                }
            }
            assert(called);
            verify(dispatcher, times(1)).forward(request, response);
        }
    }
}
